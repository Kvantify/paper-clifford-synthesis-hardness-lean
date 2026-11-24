/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridBoundaryCuts
public import GridHardness.OrbitSplicing

/-!
# Region Contraction

Contract a partition of an actual Hamiltonian graph when each region has
at most three boundary edges. The partition is a surjective vertex labelling;
the hypotheses concern graph edges, not the traversal to be extracted.
For a grid assembly, every tentacle can be assigned to its even-side cluster,
leaving at most three outside edges per resulting cluster region.
-/

@[expose] public section

set_option autoImplicit false

namespace GridHardness.RegionContraction
open SimpleGraph

section
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def region (label : V → C) (c : C) : Finset V := Finset.univ.filter (fun v => label v = c)

omit [DecidableEq V] [Fintype C] in
@[simp] theorem mem_region (label : V → C) (c : C) (v : V) :
    v ∈ region label c ↔ label v = c := by simp [region]

omit [DecidableEq V] [Fintype C] in
theorem region_nonempty (label : V → C) (hs : Function.Surjective label) (c : C) :
    (region label c).Nonempty := by
  obtain ⟨v,hv⟩ := hs c
  exact ⟨v,(mem_region label c v).mpr hv⟩

omit [DecidableEq V] [Fintype C] in
theorem region_proper [Nontrivial C] (label : V → C) (hs : Function.Surjective label) (c : C) :
    ∃ v, v ∉ region label c := by
  obtain ⟨d,hd⟩ := exists_ne c
  obtain ⟨v,hv⟩ := hs d
  exact ⟨v,by simpa only [mem_region,hv] using hd⟩

/-- A unique exit per region turns every ambient step into a stutter or
one step of an actual spanning successor permutation on the region labels. -/
theorem contract_unique_exit (label : V → C) (hs : Function.Surjective label)
    (step : Equiv.Perm V) (ho : OneOrbit step)
    (hx : ∀ c, (CycleCut.leaving step (region label c)).card = 1) :
    ∃ next : Equiv.Perm C, OneOrbit next ∧
      (∀ v, label (step v) = label v ∨ label (step v) = next (label v)) ∧
      (∀ c, ∃ v, label v = c ∧ label (step v) = next c ∧ next c ≠ c) := by
  classical
  choose exit hexit using (fun c => Finset.card_eq_one.mp (hx c))
  have he (c : C) : label (exit c) = c ∧ label (step (exit c)) ≠ c := by
    have hm : exit c ∈ CycleCut.leaving step (region label c) := by rw [hexit c]; simp
    simpa only [CycleCut.leaving, Finset.mem_filter, mem_region] using hm
  let next : C → C := fun c => label (step (exit c))
  have hproject (v : V) : label (step v) = label v ∨ label (step v) = next (label v) := by
    by_cases hv : label (step v) = label v
    · exact Or.inl hv
    · apply Or.inr
      have hm : v ∈ CycleCut.leaving step (region label (label v)) := by
        simp only [CycleCut.leaving, Finset.mem_filter, mem_region]
        exact ⟨True.intro,hv⟩
      rw [hexit (label v), Finset.mem_singleton] at hm
      exact congrArg (fun w => label (step w)) hm
  have hn : OneOrbit next := ho.project label hs hproject
  refine ⟨Equiv.ofBijective next hn.bijective, hn, hproject, ?_⟩
  intro c
  exact ⟨exit c,(he c).1,rfl,(he c).2⟩

/-- Actual graph boundary bounds discharge the unique-exit hypothesis. -/
theorem contract_three_edges [Nontrivial C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : V → C) (hs : Function.Surjective label)
    (step : Equiv.Perm V) (ho : OneOrbit step) (ha : ∀ v, G.Adj v (step v))
    (hv : 3 ≤ Fintype.card V)
    (hb : ∀ c, (CycleCut.boundary G (region label c)).card ≤ 3) :
    ∃ next : Equiv.Perm C, OneOrbit next ∧
      (∀ v, label (step v) = label v ∨ label (step v) = next (label v)) ∧
      (∀ c, ∃ v, label v = c ∧ label (step v) = next c ∧ next c ≠ c) := by
  apply contract_unique_exit label hs step ho
  intro c
  exact (CycleCut.three_edge_boundary G step ho ha hv (region label c)
    (region_nonempty label hs c) (region_proper label hs c) (hb c)).1

/-- Contracting regions of boundary size at most three preserves a
Hamiltonian cycle in any source graph containing their actual inter-region
edges. In particular this is the reverse direction needed by grid assembly. -/
theorem hamiltonianCycle_contract
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph C)
    (label : V → C) (hs : Function.Surjective label)
    (hc : 3 ≤ Fintype.card C)
    (hb : ∀ c, (CycleCut.boundary G (region label c)).card ≤ 3)
    (he : ∀ u v, G.Adj u v → label u ≠ label v → H.Adj (label u) (label v))
    (hh : ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle) :
    ∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle := by
  have hv : 3 ≤ Fintype.card V := hc.trans (Fintype.card_le_of_surjective label hs)
  let : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨step,ho,ha⟩ := (hamiltonianCycle_iff_oneOrbit G hv).mp hh
  obtain ⟨next,hn,_,hnext⟩ := contract_three_edges G label hs step ho ha hv hb
  apply (hamiltonianCycle_iff_oneOrbit H hc).mpr
  refine ⟨next,hn,?_⟩
  intro c
  obtain ⟨v,hv,hstep,hne⟩ := hnext c
  have hadj := he v (step v) (ha v) (by rw [hv,hstep]; exact hne.symm)
  simpa only [hv,hstep] using hadj

/-- At most one actual undirected edge joins each pair of distinct regions.
This is an adjacency condition, independent of the Hamiltonian cycle. -/
def UniqueBetween (G : SimpleGraph V) (label : V → C) : Prop :=
  ∀ u v u' v', G.Adj u v → G.Adj u' v' → label u ≠ label v →
    label u = label u' → label v = label v' → u = u' ∧ v = v'

/-- A simple interface between regions transfers the source degree bound
to the number of actual graph edges on each region boundary. -/
theorem boundary_card_le_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph C) [DecidableRel H.Adj]
    (label : V → C)
    (he : ∀ u v, G.Adj u v → label u ≠ label v → H.Adj (label u) (label v))
    (hu : UniqueBetween G label) (c : C) :
    (CycleCut.boundary G (region label c)).card ≤ H.degree c := by
  have hmem {e : V×V} (h : e ∈ CycleCut.boundary G (region label c)) :
      label e.1 = c ∧ label e.2 ≠ c ∧ G.Adj e.1 e.2 := by
    obtain ⟨hp,ha⟩ := Finset.mem_filter.mp h
    obtain ⟨hi,ho⟩ := Finset.mem_product.mp hp
    exact ⟨(mem_region label c e.1).mp hi,
      fun h => (Finset.mem_sdiff.mp ho).2 ((mem_region label c e.2).mpr h),ha⟩
  change (CycleCut.boundary G (region label c)).card ≤ (H.neighborFinset c).card
  apply Finset.card_le_card_of_injOn (fun e : V×V => label e.2)
  · intro e hm
    have h := hmem hm
    apply (H.mem_neighborFinset c (label e.2)).mpr
    have hh := he e.1 e.2 h.2.2 (by rw [h.1]; exact h.2.1.symm)
    simpa only [h.1] using hh
  · intro e hm f hn heq
    have h := hmem hm
    have k := hmem hn
    obtain ⟨hl,hr⟩ := hu e.1 e.2 f.1 f.2 h.2.2 k.2.2
      (by rw [h.1]; exact h.2.1.symm) (h.1.trans k.1.symm) heq
    exact Prod.ext hl hr

/-- A subcubic source graph with one physical edge per inter-region
attachment supplies all cut bounds needed for cycle extraction. -/
theorem hamiltonianCycle_contract_of_subcubic
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph C) [DecidableRel H.Adj]
    (label : V → C) (hs : Function.Surjective label)
    (hc : 3 ≤ Fintype.card C) (hd : ∀ c, H.degree c ≤ 3)
    (he : ∀ u v, G.Adj u v → label u ≠ label v → H.Adj (label u) (label v))
    (hu : UniqueBetween G label)
    (hh : ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle) :
    ∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle :=
  hamiltonianCycle_contract G H label hs hc
    (fun c => (boundary_card_le_degree G H label he hu c).trans (hd c)) he hh

end
end GridHardness.RegionContraction
