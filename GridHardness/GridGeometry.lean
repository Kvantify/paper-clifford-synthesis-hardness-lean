/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CycleToPath
public import GridProblems.Source
public import Mathlib.Data.Finset.Max

/-!
# Grid Geometry

Manhattan adjacency, grid corners, and degree-two vertices of Hamiltonian grids.
-/

@[expose] public section

namespace GridHardness
open CliffordSynthesis SimpleGraph SimpleGraph.Walk

instance gridDecidable {m : Nat} (point : Fin (m + 1) → Int × Int) :
    DecidableRel (IntegerGrid.graph point).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = (1 : Nat)))

/-- Unit Manhattan distance has precisely the four lattice directions. -/
theorem manhattan_one_iff (p q : Int × Int) :
    IntegerGrid.manhattan p q = 1 ↔
      q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨
      q = (p.1, p.2 + 1) ∨ q = (p.1, p.2 - 1) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [IntegerGrid.manhattan, Nat.add_eq_one_iff, Int.natAbs_eq_iff,
    Int.natCast_zero, Int.natCast_one, neg_zero, Prod.mk.injEq]
  omega

/-- A vertex minimizing `x+y` has at most two neighbours in an induced grid.
Injectivity matters: labels with repeated coordinates would spoil this bound. -/
theorem corner_degree_le_two {m : Nat} (point : Fin (m + 1) → Int × Int)
    (hp : Function.Injective point) (s : Fin (m + 1))
    (hmin : ∀ v, (point s).1 + (point s).2 ≤ (point v).1 + (point v).2) :
    (IntegerGrid.graph point).degree s ≤ 2 := by
  let G := IntegerGrid.graph point
  have hsub : (G.neighborFinset s).image point ⊆
      {((point s).1 + 1, (point s).2), ((point s).1, (point s).2 + 1)} := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    have ha : IntegerGrid.manhattan (point s) (point v) = 1 :=
      (G.mem_neighborFinset s v).mp hv
    have hm := hmin v
    rcases (manhattan_one_iff _ _).mp ha with h | h | h | h
    · simp [h]
    · rw [h] at hm
      dsimp at hm
      omega
    · simp [h]
    · rw [h] at hm
      dsimp at hm
      omega
  change (G.neighborFinset s).card ≤ 2
  rw [← Finset.card_image_of_injective _ hp]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Every nonempty finite induced grid has a vertex of degree at most two. -/
theorem exists_corner {m : Nat} (point : Fin (m + 1) → Int × Int)
    (hp : Function.Injective point) :
    ∃ s, (IntegerGrid.graph point).degree s ≤ 2 := by
  obtain ⟨s, _, hs⟩ := Finset.exists_min_image Finset.univ
    (fun v => (point v).1 + (point v).2) Finset.univ_nonempty
  exact ⟨s, corner_degree_le_two point hp s (fun v => hs v (Finset.mem_univ v))⟩

/-- A Hamiltonian cycle forces degree at least two at every vertex. -/
theorem two_le_degree_of_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a : V} {p : G.Walk a a}
    (hp : p.IsHamiltonianCycle) (s : V) : 2 ≤ G.degree s := by
  have h := Set.ncard_le_ncard (p.toSubgraph.neighborSet_subset s) (Set.toFinite _)
  rw [hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support s)] at h
  simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    card_neighborSet_eq_degree] using h

/-- The degree-two vertex used in the classical grid argument always exists
on a yes-instance. `SelectMarking.lean` uses this existence theorem to prove
completeness of a certified search over vertex pairs. -/
theorem grid_cycle_has_degree_two {m : Nat} (point : Fin (m + 1) → Int × Int)
    (hp : Function.Injective point)
    (hc : ∃ a, ∃ p : (IntegerGrid.graph point).Walk a a, p.IsHamiltonianCycle) :
    ∃ s, (IntegerGrid.graph point).degree s = 2 := by
  obtain ⟨s, hs⟩ := exists_corner point hp
  obtain ⟨a, p, hpcycle⟩ := hc
  exact ⟨s, le_antisymm hs (two_le_degree_of_cycle hpcycle s)⟩

end GridHardness
