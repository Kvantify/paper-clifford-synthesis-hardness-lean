/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyPartition

/-!
# Grid Assembly Geometry

A finite coordinate certificate for assembling clusters and their owned
tentacles. Validity contains only finite geometric predicates: docking,
separation, designated ports and exact inter-region boundary sets.
-/

@[expose] public section

namespace GridHardness.GridAssembly
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

local instance : DecidableRel lattice.Adj := fun p q =>
  inferInstanceAs (Decidable (IntegerGrid.manhattan p q = 1))

structure Layout (C : Type*) where
  body : C → Body
  port : C → C → Point

namespace Layout
variable {C : Type*} [Fintype C]

def region (l : Layout C) (c : C) : Finset Point := (l.body c).points

def points (l : Layout C) : Finset Point := Finset.univ.biUnion l.region

abbrev Vertex (l : Layout C) := {p : Point // p ∈ l.points}

def graph (l : Layout C) : SimpleGraph l.Vertex := finiteGrid l.points

instance (l : Layout C) : DecidableRel l.graph.Adj := fun p q =>
  inferInstanceAs (Decidable (IntegerGrid.manhattan p.val q.val = 1))

/-- Alternating ownership assigns every arm to one side of the source
bipartition. The last field computes the entire actual lattice boundary,
so it excludes unintended inter-region contacts as well as missing edges. -/
structure Valid (l : Layout C) (H : SimpleGraph C) [DecidableRel H.Adj] : Prop where
  bodies : ∀ c, (l.body c).Valid
  disjoint : ∀ c d, c ≠ d → Disjoint (l.region c) (l.region d)
  oppositeOwners : ∀ c d, H.Adj c d → (l.body c).ownsTentacles ≠ (l.body d).ownsTentacles
  ports : ∀ c d, H.Adj c d → (l.body c).IsPort (l.port c d)
  distinctPorts : ∀ c d e, H.Adj c d → H.Adj c e → d ≠ e → l.port c d ≠ l.port c e
  boundaries : ∀ c d, c ≠ d →
    TwoClusterAssembly.boundary (l.region c) (l.region d) =
      if H.Adj c d then {(l.port c d, l.port d c)} else ∅

instance [DecidableEq C] (l : Layout C) (H : SimpleGraph C) [DecidableRel H.Adj] : Decidable (l.Valid H) := by
  letI : Decidable (∀ c, (l.body c).Valid) := inferInstance
  letI : Decidable (∀ c d, c ≠ d → Disjoint (l.region c) (l.region d)) := inferInstance
  letI : Decidable (∀ c d, H.Adj c d → (l.body c).ownsTentacles ≠
    (l.body d).ownsTentacles) := inferInstance
  letI : Decidable (∀ c d, H.Adj c d → (l.body c).IsPort (l.port c d)) := inferInstance
  letI : Decidable (∀ c d e, H.Adj c d → H.Adj c e → d ≠ e →
    l.port c d ≠ l.port c e) := inferInstance
  letI : Decidable (∀ c d, c ≠ d →
    TwoClusterAssembly.boundary (l.region c) (l.region d) =
      if H.Adj c d then {(l.port c d, l.port d c)} else ∅) := inferInstance
  exact decidable_of_iff
    ((∀ c, (l.body c).Valid) ∧
      (∀ c d, c ≠ d → Disjoint (l.region c) (l.region d)) ∧
      (∀ c d, H.Adj c d → (l.body c).ownsTentacles ≠ (l.body d).ownsTentacles) ∧
      (∀ c d, H.Adj c d → (l.body c).IsPort (l.port c d)) ∧
      (∀ c d e, H.Adj c d → H.Adj c e → d ≠ e → l.port c d ≠ l.port c e) ∧
      (∀ c d, c ≠ d → TwoClusterAssembly.boundary (l.region c) (l.region d) =
        if H.Adj c d then {(l.port c d, l.port d c)} else ∅))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
      fun h => ⟨h.bodies, h.disjoint, h.oppositeOwners, h.ports, h.distinctPorts, h.boundaries⟩⟩

theorem mem_points (l : Layout C) (p : Point) : p ∈ l.points ↔ ∃ c, p ∈ l.region c := by
  simp only [points, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem region_subset (l : Layout C) (c : C) : l.region c ⊆ l.points :=
  fun _ hp => (l.mem_points _).mpr ⟨c, hp⟩

noncomputable def label (l : Layout C) (v : l.Vertex) : C :=
  Classical.choose ((l.mem_points v.val).mp v.property)

theorem label_mem (l : Layout C) (v : l.Vertex) : v.val ∈ l.region (l.label v) :=
  Classical.choose_spec ((l.mem_points v.val).mp v.property)

namespace Valid
variable {l : Layout C} {H : SimpleGraph C} [DecidableRel H.Adj] (hv : l.Valid H)
include hv

theorem label_eq_of_mem (v : l.Vertex) {c : C} (hp : v.val ∈ l.region c) : l.label v = c := by
  by_contra hn
  exact Finset.disjoint_left.mp (hv.disjoint _ _ hn) (l.label_mem v) hp

theorem label_iff_mem (v : l.Vertex) (c : C) : l.label v = c ↔ v.val ∈ l.region c :=
  ⟨fun h => h ▸ l.label_mem v, hv.label_eq_of_mem v⟩

theorem label_surjective : Function.Surjective l.label := by
  intro c
  let v : l.Vertex := ⟨(l.body c).anchor, l.region_subset c ((l.body c).anchor_mem)⟩
  exact ⟨v, hv.label_eq_of_mem v ((l.body c).anchor_mem)⟩

omit [Fintype C] in
theorem adjacent_regions_iff {c d : C} (hcd : c ≠ d) {p q : Point}
    (hp : p ∈ l.region c) (hq : q ∈ l.region d) :
    lattice.Adj p q ↔ H.Adj c d ∧ p = l.port c d ∧ q = l.port d c := by
  have hb := hv.boundaries c d hcd
  constructor
  · intro ha
    have hm : (p, q) ∈ TwoClusterAssembly.boundary (l.region c) (l.region d) :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, ha⟩
    rw [hb] at hm
    by_cases he : H.Adj c d
    · rw [ite_eq_left he] at hm
      have heq := Finset.mem_singleton.mp hm
      exact ⟨he, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    · simp only [ite_eq_right he, Finset.notMem_empty] at hm
  · rintro ⟨he, rfl, rfl⟩
    have hm : (l.port c d, l.port d c) ∈
        TwoClusterAssembly.boundary (l.region c) (l.region d) := by
      rw [hb, ite_eq_left he]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hm).2

theorem inter_region_edge (u v : l.Vertex) (ha : l.graph.Adj u v)
    (hne : l.label u ≠ l.label v) : H.Adj (l.label u) (l.label v) :=
  ((hv.adjacent_regions_iff hne (l.label_mem u) (l.label_mem v)).mp ha).1

theorem unique_between : RegionContraction.UniqueBetween l.graph l.label := by
  intro u v u' v' ha ha' hne hu hv'
  have h := (hv.adjacent_regions_iff hne (l.label_mem u) (l.label_mem v)).mp ha
  have h' := (hv.adjacent_regions_iff hne
    (show u'.val ∈ l.region (l.label u) from hu.symm ▸ l.label_mem u')
    (show v'.val ∈ l.region (l.label v) from hv'.symm ▸ l.label_mem v')).mp ha'
  exact ⟨Subtype.ext (h.2.1.trans h'.2.1.symm), Subtype.ext (h.2.2.trans h'.2.2.symm)⟩

/-- Totalize port vertices with the regional anchor away from source edges. -/
def portVertex (c d : C) : l.Vertex :=
  if he : H.Adj c d then
    ⟨l.port c d, l.region_subset c ((l.body c).port_mem (hv.bodies c) _ (hv.ports c d he))⟩
  else ⟨(l.body c).anchor, l.region_subset c ((l.body c).anchor_mem)⟩

theorem portVertex_val {c d : C} (he : H.Adj c d) : (hv.portVertex c d).val = l.port c d := by
  simp only [portVertex, dite_eq_left he]

theorem portVertex_region {c d : C} (he : H.Adj c d) :
    (hv.portVertex c d).val ∈ l.region c := by
  rw [hv.portVertex_val he]
  exact (l.body c).port_mem (hv.bodies c) _ (hv.ports c d he)

theorem port_edge (c d : C) (he : H.Adj c d) :
    l.graph.Adj (hv.portVertex c d) (hv.portVertex d c) := by
  apply (hv.adjacent_regions_iff he.ne (hv.portVertex_region he)
    (hv.portVertex_region he.symm)).mpr
  exact ⟨he, hv.portVertex_val he, hv.portVertex_val he.symm⟩

/-- Regional paths are constructed from cluster and signed-tentacle geometry,
then lifted into the actual global induced grid. -/
theorem local_route (c d e : C) (hd : H.Adj c d) (he : H.Adj c e) (hne : d ≠ e) :
    ∃ p : l.graph.Walk (hv.portVertex c d) (hv.portVertex c e), p.IsPath ∧
      ∀ v, v ∈ p.support ↔ l.label v = c := by
  have hpd := hv.portVertex_region hd
  have hpe := hv.portVertex_region he
  have hr : HasRoute (l.region c) (hv.portVertex c d).val (hv.portVertex c e).val := by
    rw [hv.portVertex_val hd, hv.portVertex_val he]
    exact (l.body c).route (hv.bodies c) _ _ (hv.ports c d hd) (hv.ports c e he)
      (hv.distinctPorts c d e hd he hne)
  obtain ⟨p, hp, hs⟩ := lift_route (l.region_subset c) hpd hpe hr
  refine ⟨p, hp, ?_⟩
  intro v
  exact (hs v).trans (hv.label_iff_mem v c).symm

/-- The complete semantic Hamiltonian-cycle correspondence for any valid
coordinate assembly. No Hamiltonicity or local-route predicate is an input. -/
theorem hamiltonianCycle_iff [DecidableEq C] (hc : 3 ≤ Fintype.card C) (hd : ∀ c, H.degree c ≤ 3) :
    (∃ (v : l.Vertex) (p : l.graph.Walk v v), p.IsHamiltonianCycle) ↔
      ∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle :=
  RegionExpansion.hamiltonianCycle_iff_of_subcubic_ports l.graph H l.label
    hv.label_surjective hc hd hv.inter_region_edge hv.unique_between
    hv.portVertex hv.port_edge hv.local_route

theorem points_card : l.points.card =
    9 * Fintype.card C + 2 * ∑ c, (l.body c).halfTentacleSize := by
  have hp : ((Finset.univ : Finset C) : Set C).PairwiseDisjoint l.region := by
    intro c _ d _ hcd
    exact hv.disjoint c d hcd
  rw [points, Finset.card_biUnion hp]
  simp only [region, Body.points_card _ (hv.bodies _), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

theorem vertex_card : Fintype.card l.Vertex =
    9 * Fintype.card C + 2 * ∑ c, (l.body c).halfTentacleSize := by
  rw [Fintype.card_coe, hv.points_card]

end Valid
end Layout
end GridHardness.GridAssembly
