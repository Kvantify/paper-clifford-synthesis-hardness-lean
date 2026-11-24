/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCrossoverGraph

/-!
# Planar SAT Crossover

A single-orbit traversal must choose the same track through adjacent vertical segments.
-/

public section

namespace GridHardness.PlanarSatCrossover

/-- Local graph-interface conditions inherited by an isolated replacement
inside a larger graph. These express incident edges, not traversal choices. -/
structure Isolated {V : Type*} (succ : V → V) (embed : Vertex → V) : Prop where
  internal : ∀ u v, succ (embed u) = embed v → Adj u v
  outgoing : ∀ u, u ∉ exits → ∃ v, succ (embed u) = embed v
  incoming : ∀ v, v ∉ entries → ∃ u, succ (embed u) = embed v

/-- All five vertical XORs obey their actual two-route contract in any
global Hamiltonian cycle of a graph containing this isolated crossover. -/
theorem vertical_selection {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) (i : Fin 5) :
    PlanarSatXor.selection succ (embed ∘ x i) = XorGadget.leftRoute ∨
      PlanarSatXor.selection succ (embed ∘ x i) = XorGadget.rightRoute := by
  have hd : XorGadget.DegreeOK (PlanarSatXor.selection succ (embed ∘ x i)) := by
    apply PlanarSatXor.degree_of_isolation succ (embed ∘ x i) (he.comp (x_injective i))
    · intro j hj0 hj7
      obtain ⟨v, hv⟩ := hg.outgoing (x i j) (x_nonexit i j hj0 hj7)
      obtain ⟨e, he', rfl⟩ := (x_outgoing i j hj0 hj7 v).mp (hg.internal _ _ hv)
      exact ⟨e, he', hv⟩
    · intro j hj3 hj4
      obtain ⟨v, hv⟩ := hg.incoming (x i j) (x_nonentry i j hj3 hj4)
      obtain ⟨e, he', rfl⟩ := (x_incoming i j hj3 hj4 v).mp (hg.internal _ _ hv)
      exact ⟨e, he', hv⟩
  exact XorGadget.selection_of_oneOrbit succ ho (embed ∘ x i) (embed (h 0))
    (fun j hj => by have := he hj; simp [h, x] at this)
    (PlanarSatXor.selection succ (embed ∘ x i)) hd
    (fun e hb => (PlanarSatXor.selection_true _ _ _).mp hb)

theorem selection_step {V : Type*} [DecidableEq V] (succ : V → V) (embed : Vertex → V)
    (i : Fin 5) (r : XorGadget.Selection)
    (hr : PlanarSatXor.selection succ (embed ∘ x i) = r)
    (e : Fin 10) (he : r e = true) :
    succ (embed (x i (XorGadget.arc e).1)) = embed (x i (XorGadget.arc e).2) := by
  apply (PlanarSatXor.selection_true succ (embed ∘ x i) e).mp
  rw [hr]
  exact he

/-- The four actual parallel-row choices propagate the vertical signal
across all five XORs. This is proved from the ambient permutation and the
incident-edge interface, rather than imposed as a Boolean wiring constraint. -/
theorem vertical_adjacent_equal {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) (i : Fin 4) :
    PlanarSatXor.selection succ (embed ∘ x i.castSucc) =
      PlanarSatXor.selection succ (embed ∘ x i.succ) := by
  have hl := vertical_selection succ ho embed he hg i.castSucc
  have hr := vertical_selection succ ho embed he hg i.succ
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · rw [hl, hr]
  · obtain ⟨v, hv⟩ := hg.outgoing (row i false) (by simp [row, exits, h, x])
    rcases (row_outgoing i v).mp (hg.internal _ _ hv) with rfl | rfl
    · have hs := selection_step succ embed i.castSucc _ hl 6 (by decide)
      have hc := he (succ.injective (hv.trans hs.symm))
      simp [row, x, XorGadget.arc] at hc
    · have hs := selection_step succ embed i.succ _ hr 3 (by decide)
      have hc := he (succ.injective (hv.trans hs.symm))
      simp [row, x, XorGadget.arc] at hc
  · have hp : x i.castSucc 4 ∉ entries := by
      fin_cases i <;> decide
    have hq : x i.succ 3 ∉ entries := by
      fin_cases i <;> decide
    obtain ⟨u, hu⟩ := hg.incoming (x i.castSucc 4) hp
    have hu' : u = row i false := by
      rcases (upper_entry_incoming i u).mp (hg.internal _ _ hu) with rfl | heq
      · have hn : PlanarSatXor.selection succ (embed ∘ x i.castSucc) 6 = false := by
          rw [hl]; rfl
        have hy : PlanarSatXor.selection succ (embed ∘ x i.castSucc) 6 = true :=
          (PlanarSatXor.selection_true _ _ _).mpr hu
        exact False.elim (by rw [hn] at hy; contradiction)
      · exact heq
    obtain ⟨v, hv⟩ := hg.incoming (x i.succ 3) hq
    have hv' : v = row i false := by
      rcases (lower_entry_incoming i v).mp (hg.internal _ _ hv) with rfl | heq
      · have hn : PlanarSatXor.selection succ (embed ∘ x i.succ) 3 = false := by
          rw [hr]; rfl
        have hy : PlanarSatXor.selection succ (embed ∘ x i.succ) 3 = true :=
          (PlanarSatXor.selection_true _ _ _).mpr hv
        exact False.elim (by rw [hn] at hy; contradiction)
      · exact heq
    rw [hu'] at hu
    rw [hv'] at hv
    have hc := he (hu.symm.trans hv)
    simp [x] at hc
  · rw [hl, hr]

/-- Every global Hamiltonian traversal of the actual crossover has one
well-defined vertical signal shared by all five internal XOR gadgets. -/
theorem vertical_uniform {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) : ∃ top : Bool, ∀ i : Fin 5,
    PlanarSatXor.selection succ (embed ∘ x i) =
      if top then XorGadget.leftRoute else XorGadget.rightRoute := by
  have hall : ∀ i : Fin 5, PlanarSatXor.selection succ (embed ∘ x i) =
      PlanarSatXor.selection succ (embed ∘ x 0) := by
    apply Fin.induction
    · rfl
    · intro i hi
      exact (vertical_adjacent_equal succ ho embed he hg i).symm.trans hi
  rcases vertical_selection succ ho embed he hg 0 with hl | hr
  · exact ⟨true, fun i => (hall i).trans hl⟩
  · exact ⟨false, fun i => (hall i).trans hr⟩

end GridHardness.PlanarSatCrossover
