/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRoutes

/-!
# XOR Line Source

The directed XOR line graph, its boundary ports, and the isolation predicate.
-/

@[expose] public section

namespace GridHardness.XorLine.Source
open PathCover

/-- One original XOR and the separately traversed mandatory arcs. -/
abbrev Vertex (n : Nat) := Fin 8 ⊕ (Fin n × Bool)
def Adj (n : Nat) : Vertex n → Vertex n → Prop
  | .inl j,.inl k => ∃ e : Fin 10, XorGadget.arc e=(j,k)
  | .inr (i,false),.inr (k,true) => i=k
  | _,_ => False

def IsInput (n : Nat) : Vertex n → Prop
  | .inl j => j=3 ∨ j=4
  | .inr (_,b) => b=false
def IsOutput (n : Nat) : Vertex n → Prop
  | .inl j => j=0 ∨ j=7
  | .inr (_,b) => b=true

structure Isolated {V : Type*} (n : Nat) (succ : V → V) (embed : Vertex n → V) : Prop where
  internal : ∀ u v, succ (embed u)=embed v → Adj n u v
  outgoing : ∀ u, ¬IsOutput n u → ∃ v, succ (embed u)=embed v
  incoming : ∀ v, ¬IsInput n v → ∃ u, succ (embed u)=embed v

def size {n : Nat} : Channel n → Nat | none => 7 | some _ => 1
def bitEquiv : Fin 2 ≃ Bool where
  toFun := ![false,true]
  invFun := fun b => if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

def cover (n : Nat) (choice : Bool) : Cover (Channel n) (Vertex n) where
  size := size
  equiv :=
    { toFun := fun w => match w with
        | ⟨none,j⟩ => .inl (XorWire.localOrder choice j)
        | ⟨some i,j⟩ => .inr (i,bitEquiv j)
      invFun := fun w => match w with
        | .inl j => ⟨none,(XorWire.localOrder choice).symm j⟩
        | .inr (i,b) => ⟨some i,bitEquiv.symm b⟩
      left_inv := by
        rintro ⟨_ | i,j⟩
        · exact congrArg (fun k : Fin 8 => (⟨none,k⟩ : Blocks (@size n)))
            ((XorWire.localOrder choice).symm_apply_apply j)
        · exact congrArg (fun k : Fin 2 => (⟨some i,k⟩ : Blocks (@size n)))
            (bitEquiv.symm_apply_apply j)
      right_inv := by rintro (j | ⟨i,b⟩) <;> simp }

theorem cover_internalEdges (n : Nat) (choice : Bool) (R : Vertex n → Vertex n → Prop)
    (hl : ∀ j : Fin 7,
      R (.inl (XorWire.localOrder choice j.castSucc)) (.inl (XorWire.localOrder choice j.succ)))
    (hr : ∀ i : Fin n, R (.inr (i,false)) (.inr (i,true))) :
    (cover n choice).InternalEdges R := by
  rintro (_ | i) j
  · exact hl j
  · change Fin 1 at j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact hr i

theorem cover_adjacent (n : Nat) (choice : Bool) : (cover n choice).InternalEdges (Adj n) := by
  apply cover_internalEdges
  · intro j
    obtain ⟨e,_,he⟩ := XorWire.local_route_steps choice j
    exact ⟨e,he⟩
  · intro i
    rfl

theorem xor_selection {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    PlanarSatXor.selection succ (embed ∘ Sum.inl)=XorGadget.leftRoute ∨
      PlanarSatXor.selection succ (embed ∘ Sum.inl)=XorGadget.rightRoute := by
  have hi : Function.Injective (embed ∘ Sum.inl) := he.comp Sum.inl_injective
  have hd : XorGadget.DegreeOK (PlanarSatXor.selection succ (embed ∘ Sum.inl)) := by
    apply PlanarSatXor.degree_of_isolation succ _ hi
    · intro j hj0 hj7
      obtain ⟨v,hv⟩ := hg.outgoing (.inl j) (by simp [IsOutput,hj0,hj7])
      have ha := hg.internal _ _ hv
      cases v with
      | inl k =>
        obtain ⟨e,he⟩ := ha
        exact ⟨e,congrArg Prod.fst he,by simpa [Function.comp_def,he] using hv⟩
      | inr p => rcases p with ⟨i,b⟩; cases b <;> exact False.elim ha
    · intro j hj3 hj4
      obtain ⟨v,hv⟩ := hg.incoming (.inl j) (by simp [IsInput,hj3,hj4])
      have ha := hg.internal _ _ hv
      cases v with
      | inl k =>
        obtain ⟨e,he⟩ := ha
        exact ⟨e,congrArg Prod.snd he,by simpa [Function.comp_def,he] using hv⟩
      | inr p => rcases p with ⟨i,b⟩; cases b <;> exact False.elim ha
  exact XorGadget.selection_of_oneOrbit_injective succ ho _ hi _ hd
    (fun e hb => (PlanarSatXor.selection_true _ _ _).mp hb)

theorem row_step {n : Nat} {V : Type*} (succ : V → V) (embed : Vertex n → V)
    (hg : Isolated n succ embed) (i : Fin n) :
    succ (embed (.inr (i,false)))=embed (.inr (i,true)) := by
  obtain ⟨v,hv⟩ := hg.outgoing (.inr (i,false)) (by simp [IsOutput])
  have ha := hg.internal _ _ hv
  cases v with
  | inl j => exact False.elim ha
  | inr p =>
    rcases p with ⟨k,b⟩
    cases b
    · exact False.elim ha
    · have hk : i=k := ha
      simpa [hk] using hv

theorem route_classification {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ choice : Bool, (cover n choice).InternalEdges (fun u v => succ (embed u)=embed v) := by
  have hu := xor_selection succ ho embed he hg
  obtain ⟨choice,hc⟩ : ∃ choice : Bool,
      PlanarSatXor.selection succ (embed ∘ Sum.inl)=XorWire.route choice := by
    rcases hu with hl | hr
    · exact ⟨true,hl⟩
    · exact ⟨false,hr⟩
  refine ⟨choice,cover_internalEdges n choice _ ?_ (row_step succ embed hg)⟩
  intro j
  obtain ⟨e,hs,ha⟩ := XorWire.local_route_steps choice j
  rw [← hc] at hs
  have hh := (PlanarSatXor.selection_true succ (embed ∘ Sum.inl) e).mp hs
  simpa only [ha,Function.comp_def] using hh

end GridHardness.XorLine.Source
