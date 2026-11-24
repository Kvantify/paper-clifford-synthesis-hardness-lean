/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLinePaths

/-!
# XOR Line Routes

Classify the Hamiltonian route through an XOR line by its endpoints and channel.
-/

public section

namespace GridHardness.XorLine

theorem zero_outgoing {n : Nat} (i : Fin n) (v : Vertex n) :
    Adj n (x i.succ 0) v ↔ v=x i.succ 1 ∨ v=row i true := by
  rcases v with ⟨k,j⟩ | ⟨r,b⟩
  · have ht : ∀ j : Fin 8, (∃ e : Fin 10, XorGadget.arc e=(0,j)) ↔ j=1 := by decide
    change (i.succ=k ∧ ∃ e : Fin 10, XorGadget.arc e=(0,j)) ↔ _
    rw [ht]
    simp [row,x,Prod.ext_iff,eq_comm]
  · cases b <;> simp [Adj,row,x,Prod.ext_iff,eq_comm]

theorem seven_outgoing {n : Nat} (i : Fin n) (v : Vertex n) :
    Adj n (x i.castSucc 7) v ↔ v=x i.castSucc 6 ∨ v=row i true := by
  rcases v with ⟨k,j⟩ | ⟨r,b⟩
  · have ht : ∀ j : Fin 8, (∃ e : Fin 10, XorGadget.arc e=(7,j)) ↔ j=6 := by decide
    change (i.castSucc=k ∧ ∃ e : Fin 10, XorGadget.arc e=(7,j)) ↔ _
    rw [ht]
    simp [row,x,Prod.ext_iff,eq_comm]
  · cases b <;> simp [Adj,row,x,Prod.ext_iff,eq_comm]

theorem row_start {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (embed : Vertex n → V) (he : Function.Injective embed)
    (hg : Isolated n succ embed) (choice : Bool)
    (hc : ∀ i : Fin (n+1), PlanarSatXor.selection succ (embed ∘ x i)=
      if choice then XorGadget.leftRoute else XorGadget.rightRoute) (i : Fin n) :
    succ (embed (row i false))=
      embed (x (sectionEquiv n choice (some i)) (XorWire.localOrder choice 0)) := by
  rw [section_some]
  obtain ⟨v,hv⟩ := hg.outgoing (row i false) (by simp [IsOutput,row])
  cases choice
  · rcases (row_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · exact hv
    · have hs := selection_step succ embed i.succ _ (hc i.succ) 3 (by decide)
      have h := he (succ.injective (hv.trans hs.symm))
      simp [row,x,XorGadget.arc] at h
  · rcases (row_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · have hs := selection_step succ embed i.castSucc _ (hc i.castSucc) 6 (by decide)
      have h := he (succ.injective (hv.trans hs.symm))
      simp [row,x,XorGadget.arc] at h
    · exact hv

theorem row_finish {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (embed : Vertex n → V)
    (hg : Isolated n succ embed) (choice : Bool)
    (hc : ∀ i : Fin (n+1), PlanarSatXor.selection succ (embed ∘ x i)=
      if choice then XorGadget.leftRoute else XorGadget.rightRoute) (i : Fin n) :
    succ (embed (x (sectionEquiv n choice (some i)) (XorWire.localOrder choice 7)))=
      embed (row i true) := by
  rw [section_some]
  cases choice
  · have hn : ¬IsOutput n (x i.castSucc 7) := by
      have hne : i.castSucc ≠ Fin.last n := i.castSucc_ne_last
      simp [IsOutput,x,hne]
    obtain ⟨v,hv⟩ := hg.outgoing (x i.castSucc 7) hn
    rcases (seven_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · have hh := (PlanarSatXor.selection_true succ (embed ∘ x i.castSucc) 9).mpr hv
      rw [hc i.castSucc] at hh
      contradiction
    · exact hv
  · obtain ⟨v,hv⟩ := hg.outgoing (x i.succ 0) (by simp [IsOutput,x])
    rcases (zero_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · have hh := (PlanarSatXor.selection_true succ (embed ∘ x i.succ) 0).mpr hv
      rw [hc i.succ] at hh
      contradiction
    · exact hv

/-- Complete local classification extracted from the actual ambient cycle.
No selected signal or intended traversal is an input to this theorem. -/
theorem route_classification {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ choice : Bool, (cover n choice).InternalEdges
      (fun u v => succ (embed u)=embed v) := by
  obtain ⟨choice,hc⟩ := uniform_selection succ ho embed he hg
  refine ⟨choice,cover_internalEdges n choice _ ?_ ?_ ?_⟩
  · intro i j
    obtain ⟨e,hs,ha⟩ := XorWire.local_route_steps choice j
    change (if choice then XorGadget.leftRoute else XorGadget.rightRoute) e=true at hs
    have hh := selection_step succ embed i _ (hc i) e hs
    simpa only [ha] using hh
  · exact row_start succ embed he hg choice hc
  · exact row_finish succ embed hg choice hc

end GridHardness.XorLine
