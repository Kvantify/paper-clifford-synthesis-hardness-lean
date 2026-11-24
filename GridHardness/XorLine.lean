/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorRouting

/-!
# XOR Line

Refining an exclusive-or constraint line across mandatory arcs.

Unlike serial `XorWire`, this construction preserves a separate traversal
for every crossed arc. A selected original endpoint traverses the first or
last XOR; each crossed arc traverses one of the intervening XORs. These are
the parallel branches in Bosboom et al., Figure 8.
-/

@[expose] public section

namespace GridHardness.XorLine

abbrev Vertex (n : Nat) := (Fin (n+1) × Fin 8) ⊕ (Fin n × Bool)
def x {n : Nat} (i : Fin (n +1)) (j : Fin 8) : Vertex n := .inl (i,j)
def row {n : Nat} (i : Fin n) (b : Bool) : Vertex n := .inr (i,b)

def Adj (n : Nat) : Vertex n → Vertex n → Prop
  | .inl (i,j), .inl (k,l) => i=k ∧ ∃ e : Fin 10, XorGadget.arc e=(j,l)
  | .inr (r,false), .inl (i,j) => (i=r.castSucc ∧ j=4) ∨ (i=r.succ ∧ j=3)
  | .inl (i,j), .inr (r,true) => (i=r.castSucc ∧ j=7) ∨ (i=r.succ ∧ j=0)
  | _,_ => False

instance (n : Nat) : DecidableRel (Adj n) := by
  rintro (⟨i,j⟩ | ⟨r,b⟩) (⟨k,l⟩ | ⟨s,c⟩)
  · exact inferInstanceAs (Decidable (_ ∧ _))
  · cases c <;> dsimp [Adj] <;> infer_instance
  · cases b <;> dsimp [Adj] <;> infer_instance
  · cases b <;> cases c <;> dsimp [Adj] <;> infer_instance

def IsInput (n : Nat) : Vertex n → Prop
  | .inl (i,j) => (i=0 ∧ j=3) ∨ (i=Fin.last n ∧ j=4)
  | .inr (_,b) => b=false
def IsOutput (n : Nat) : Vertex n → Prop
  | .inl (i,j) => (i=0 ∧ j=0) ∨ (i=Fin.last n ∧ j=7)
  | .inr (_,b) => b=true

structure Isolated {V : Type*} (n : Nat) (succ : V → V) (embed : Vertex n → V) : Prop where
  internal : ∀ u v, succ (embed u)=embed v → Adj n u v
  outgoing : ∀ u, ¬IsOutput n u → ∃ v, succ (embed u)=embed v
  incoming : ∀ v, ¬IsInput n v → ∃ u, succ (embed u)=embed v

theorem x_injective {n : Nat} (i : Fin (n +1)) : Function.Injective (x i) := by
  intro j k h
  simpa [x] using h

theorem component_selection {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) (i : Fin (n +1)) :
    PlanarSatXor.selection succ (embed ∘ x i)=XorGadget.leftRoute ∨
      PlanarSatXor.selection succ (embed ∘ x i)=XorGadget.rightRoute := by
  have hi := he.comp (x_injective i)
  have hd : XorGadget.DegreeOK (PlanarSatXor.selection succ (embed ∘ x i)) := by
    apply PlanarSatXor.degree_of_isolation succ _ hi
    · intro j hj0 hj7
      obtain ⟨v,hv⟩ := hg.outgoing (x i j) (by simp [IsOutput,x,hj0,hj7])
      have ha := hg.internal _ _ hv
      rcases v with ⟨k,l⟩ | ⟨r,b⟩
      · obtain ⟨hik,e,hjl⟩ := ha
        subst k
        exact ⟨e,congrArg Prod.fst hjl,by simpa [Function.comp_def,x,hjl] using hv⟩
      · cases b
        · exact False.elim ha
        · rcases ha with ⟨_,hj⟩ | ⟨_,hj⟩
          · exact False.elim (hj7 hj)
          · exact False.elim (hj0 hj)
    · intro j hj3 hj4
      obtain ⟨v,hv⟩ := hg.incoming (x i j) (by simp [IsInput,x,hj3,hj4])
      have ha := hg.internal _ _ hv
      rcases v with ⟨k,l⟩ | ⟨r,b⟩
      · obtain ⟨hki,e,hlj⟩ := ha
        subst k
        exact ⟨e,congrArg Prod.snd hlj,by simpa [Function.comp_def,x,hlj] using hv⟩
      · cases b
        · rcases ha with ⟨_,hj⟩ | ⟨_,hj⟩
          · exact False.elim (hj4 hj)
          · exact False.elim (hj3 hj)
        · exact False.elim ha
  exact XorGadget.selection_of_oneOrbit_injective succ ho _ hi _ hd
    (fun e hb => (PlanarSatXor.selection_true _ _ _).mp hb)

theorem row_outgoing {n : Nat} (i : Fin n) (v : Vertex n) :
    Adj n (row i false) v ↔ v=x i.castSucc 4 ∨ v=x i.succ 3 := by
  rcases v with ⟨k,j⟩ | ⟨r,b⟩
  · simp [Adj,row,x,Prod.ext_iff]
  · cases b <;> simp [Adj,row,x]

theorem upper_incoming {n : Nat} (i : Fin n) (v : Vertex n) :
    Adj n v (x i.castSucc 4) ↔ v=x i.castSucc 5 ∨ v=row i false := by
  rcases v with ⟨k,j⟩ | ⟨r,b⟩
  · have ht : ∀ j : Fin 8, (∃ e : Fin 10, XorGadget.arc e=(j,4)) ↔ j=5 := by decide
    change (k=i.castSucc ∧ ∃ e : Fin 10, XorGadget.arc e=(j,4)) ↔ _
    rw [ht]
    simp [row,x,Prod.ext_iff]
  · cases b
    · simp [Adj,row,x,Prod.ext_iff,eq_comm]
    · simp [Adj,row,x]

theorem lower_incoming {n : Nat} (i : Fin n) (v : Vertex n) :
    Adj n v (x i.succ 3) ↔ v=x i.succ 2 ∨ v=row i false := by
  rcases v with ⟨k,j⟩ | ⟨r,b⟩
  · have ht : ∀ j : Fin 8, (∃ e : Fin 10, XorGadget.arc e=(j,3)) ↔ j=2 := by decide
    change (k=i.succ ∧ ∃ e : Fin 10, XorGadget.arc e=(j,3)) ↔ _
    rw [ht]
    simp [row,x,Prod.ext_iff]
  · cases b
    · simp [Adj,row,x,Prod.ext_iff,eq_comm]
    · simp [Adj,row,x]

theorem selection_step {n : Nat} {V : Type*} [DecidableEq V]
    (succ : V → V) (embed : Vertex n → V) (i : Fin (n +1))
    (r : XorGadget.Selection) (hr : PlanarSatXor.selection succ (embed ∘ x i) =r)
    (e : Fin 10) (hb : r e =true) :
    succ (embed (x i (XorGadget.arc e).1))=embed (x i (XorGadget.arc e).2) := by
  apply (PlanarSatXor.selection_true succ (embed ∘ x i) e).mp
  rw [hr]
  exact hb

theorem adjacent_equal {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) (i : Fin n) :
    PlanarSatXor.selection succ (embed ∘ x i.castSucc)=
      PlanarSatXor.selection succ (embed ∘ x i.succ) := by
  have hl := component_selection succ ho embed he hg i.castSucc
  have hr := component_selection succ ho embed he hg i.succ
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · rw [hl,hr]
  · obtain ⟨v,hv⟩ := hg.outgoing (row i false) (by simp [IsOutput,row])
    rcases (row_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · have hs := selection_step succ embed i.castSucc _ hl 6 (by decide)
      have hc := he (succ.injective (hv.trans hs.symm))
      simp [row,x,XorGadget.arc] at hc
    · have hs := selection_step succ embed i.succ _ hr 3 (by decide)
      have hc := he (succ.injective (hv.trans hs.symm))
      simp [row,x,XorGadget.arc] at hc
  · have hp : ¬IsInput n (x i.castSucc 4) := by
      have hne : i.castSucc ≠ Fin.last n := by
        intro h
        have hh := congrArg Fin.val h
        have hi := i.isLt
        simp only [Fin.val_castSucc,Fin.val_last] at hh
        omega
      simp [IsInput,x,hne]
    have hq : ¬IsInput n (x i.succ 3) := by simp [IsInput,x]
    obtain ⟨u,hu⟩ := hg.incoming (x i.castSucc 4) hp
    have hu' : u=row i false := by
      rcases (upper_incoming i u).mp (hg.internal _ _ hu) with rfl | h
      · have hy := (PlanarSatXor.selection_true succ (embed ∘ x i.castSucc) 6).mpr hu
        rw [hl] at hy
        contradiction
      · exact h
    obtain ⟨v,hv⟩ := hg.incoming (x i.succ 3) hq
    have hv' : v=row i false := by
      rcases (lower_incoming i v).mp (hg.internal _ _ hv) with rfl | h
      · have hy := (PlanarSatXor.selection_true succ (embed ∘ x i.succ) 3).mpr hv
        rw [hr] at hy
        contradiction
      · exact h
    rw [hu'] at hu
    rw [hv'] at hv
    have hc := he (hu.symm.trans hv)
    simp [x] at hc
  · rw [hl,hr]

theorem uniform_selection {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ top : Bool, ∀ i : Fin (n+1), PlanarSatXor.selection succ (embed ∘ x i)=
      if top then XorGadget.leftRoute else XorGadget.rightRoute := by
  have hall : ∀ i : Fin (n+1), PlanarSatXor.selection succ (embed ∘ x i)=
      PlanarSatXor.selection succ (embed ∘ x 0) := by
    apply Fin.induction
    · rfl
    · intro i hi
      exact (adjacent_equal succ ho embed he hg i).symm.trans hi
  rcases component_selection succ ho embed he hg 0 with hl | hr
  · exact ⟨true,fun i => (hall i).trans hl⟩
  · exact ⟨false,fun i => (hall i).trans hr⟩

end GridHardness.XorLine
