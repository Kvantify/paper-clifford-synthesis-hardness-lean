/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.NineClusterAttachment

/-!
# Two Cluster Assembly

A signed tentacle docked at both ends between two placed nine-clusters.
The interface records only finite coordinate-set separation and exact lattice
boundary edges. Cross routing is then constructed from the proved cluster and
tentacle routes, producing a Hamiltonian path in the actual induced grid.
-/

@[expose] public section

namespace GridHardness.TwoClusterAssembly
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

abbrev cluster (f : Frame) : Finset Point := NineClusterAttachment.points.image f.map
abbrev corner (f : Frame) (s : Fin 4) : Point := f.map (NineClusterAttachment.corner s)
abbrev mate (f : Frame) (s : Fin 4) : Point := f.map (NineClusterAttachment.mate s)

theorem corner_mem (f : Frame) (s : Fin 4) : corner f s ∈ cluster f :=
  Finset.mem_image.mpr ⟨_, NineClusterAttachment.corner_mem s, rfl⟩

theorem mate_mem (f : Frame) (s : Fin 4) : mate f s ∈ cluster f :=
  Finset.mem_image.mpr ⟨_, NineClusterAttachment.mate_mem s, rfl⟩

theorem mem_cluster_iff (f : Frame) (p : Point) : p ∈ cluster f ↔
    0 ≤ (f.unmap p).1 ∧ (f.unmap p).1 ≤ 2 ∧
      0 ≤ (f.unmap p).2 ∧ (f.unmap p).2 ≤ 2 := by
  rw [← NineClusterAttachment.mem_points_iff]
  constructor
  · rintro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    simpa only [f.unmap_map] using hq
  · intro h
    exact Finset.mem_image.mpr ⟨f.unmap p, h, f.map_unmap p⟩

theorem cluster_route (f : Frame) (i j : Fin 4) (hij : i ≠ j) :
    HasRoute (cluster f) (corner f i) (corner f j) := by
  obtain ⟨p, hp, hc, _⟩ := NineClusterAttachment.cluster_route i j hij
  exact f.route ⟨p, hp, hc⟩

/-- Join two disjoint spanning paths with one actual grid edge. -/
theorem route_join {S T : Finset Point} {a b c d : Point}
    (hp : HasRoute S a b) (hq : HasRoute T c d) (hd : Disjoint S T)
    (he : lattice.Adj b c) : HasRoute (S ∪ T) a d := by
  obtain ⟨p, hp, hc⟩ := hp
  obtain ⟨q, hq, hf⟩ := hq
  have hs : ((p.concat he).append q).support = p.support ++ q.support := by
    rw [Walk.support_append_eq_support_dropLast_append, Walk.support_concat]
    simp
  refine ⟨(p.concat he).append q, ?_, ?_⟩
  · rw [Walk.isPath_def, hs]
    apply List.nodup_append'.mpr
    refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
    rw [List.disjoint_left]
    intro v hv hw
    exact Finset.disjoint_left.mp hd ((hc v).mp hv) ((hf v).mp hw)
  · intro v
    simp only [hs, List.mem_append, hc, hf, Finset.mem_union]

/-- Actual ordered lattice edges from one finite point set to another. -/
def boundary (S T : Finset Point) : Finset (Point × Point) :=
  (S.product T).filter (fun e => lattice.Adj e.1 e.2)

theorem boundary_eq_singleton {S T : Finset Point} {a b : Point}
    (ha : a ∈ S) (hb : b ∈ T)
    (h : ∀ x ∈ S, ∀ y ∈ T, lattice.Adj x y ↔ x = a ∧ y = b) :
    boundary S T = {(a, b)} := by
  ext ⟨x, y⟩
  simp only [boundary, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hm, hadj⟩
    have hm := Finset.mem_product.mp hm
    exact (h x hm.1 y hm.2).mp hadj
  · rintro ⟨rfl, rfl⟩
    exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, (h _ ha _ hb).mpr ⟨rfl, rfl⟩⟩

/-- The even-side cluster has two tentacle edges; the odd-side cluster has
one. Cluster bodies are disjoint and nonadjacent, and all boundary equalities
refer to the actual induced lattice graph, not a selected traversal. -/
def Between (d : Drawing) (f g : Frame) (s t : Fin 4) : Prop :=
  Disjoint (cluster f) d.points ∧ Disjoint (cluster g) d.points ∧
  Disjoint (cluster f) (cluster g) ∧
  (∀ a ∈ cluster f, ∀ b ∈ cluster g, ¬lattice.Adj a b) ∧
  boundary (cluster f) d.points =
    {(corner f s, d.start 0), (mate f s, d.start 1)} ∧
  boundary (cluster g) d.points = {(corner g t, d.tip 0)}

instance (d : Drawing) (f g : Frame) (s t : Fin 4) : Decidable (Between d f g s t) := by
  unfold Between boundary
  infer_instance

def points (d : Drawing) (f g : Frame) : Finset Point := cluster f ∪ d.points ∪ cluster g

private theorem boundary_adj_of_eq {S T : Finset Point} {edges : Finset (Point × Point)}
    {a b : Point} (h : boundary S T = edges) (hm : (a, b) ∈ edges) : lattice.Adj a b := by
  have hb : (a, b) ∈ boundary S T := h.symm ▸ hm
  change (a, b) ∈ (S.product T).filter (fun e => lattice.Adj e.1 e.2) at hb
  exact (Finset.mem_filter.mp hb).2

set_option backward.isDefEq.respectTransparency true in
theorem Between.start_adjacent {d : Drawing} {f g : Frame} {s t : Fin 4}
    (h : Between d f g s t) : lattice.Adj (corner f s) (d.start 0) :=
  boundary_adj_of_eq (S := cluster f) (T := d.points) (a := corner f s) (b := d.start 0)
    h.2.2.2.2.1 (Finset.mem_insert_self _ _)

set_option backward.isDefEq.respectTransparency true in
theorem Between.tip_adjacent {d : Drawing} {f g : Frame} {s t : Fin 4}
    (h : Between d f g s t) : lattice.Adj (d.tip 0) (corner g t) :=
  (boundary_adj_of_eq (S := cluster g) (T := d.points) (a := corner g t) (b := d.tip 0)
    h.2.2.2.2.2 (Finset.mem_singleton_self _)).symm

/-- Two actual corner paths are joined through the constructed signed
cross route. All three regions are visited exactly once. -/
theorem cross_route (d : Drawing) (hv : d.Valid) (f g : Frame) (s t i j : Fin 4)
    (h : Between d f g s t) (hi : i ≠ s) (hj : t ≠ j)
    (hc : color (d.start 0) ≠ color (d.tip 0)) :
    HasRoute (points d f g) (corner f i) (corner g j) := by
  have hfirst := route_join (cluster_route f i s hi) (d.cross hv 0 0 hc) h.1 h.start_adjacent
  exact route_join hfirst (cluster_route g t j hj)
    (Finset.disjoint_union_left.mpr ⟨h.2.2.1, h.2.1.symm⟩) h.tip_adjacent

theorem left_corner_mem (d : Drawing) (f g : Frame) (i : Fin 4) :
    corner f i ∈ points d f g :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (corner_mem f i))

theorem right_corner_mem (d : Drawing) (f g : Frame) (j : Fin 4) :
    corner g j ∈ points d f g := Finset.mem_union_right _ (corner_mem g j)

/-- Hamiltonian cross-route insertion in the finite induced grid, with
both cluster bodies and every tentacle vertex included. -/
theorem cross_hamiltonian (d : Drawing) (hv : d.Valid) (f g : Frame) (s t i j : Fin 4)
    (h : Between d f g s t) (hi : i ≠ s) (hj : t ≠ j)
    (hc : color (d.start 0) ≠ color (d.tip 0)) :
    ∃ p : (finiteGrid (points d f g)).Walk
      ⟨corner f i, left_corner_mem d f g i⟩ ⟨corner g j, right_corner_mem d f g j⟩,
      p.IsHamiltonian :=
  (hasRoute_iff_hamiltonian _ _).mp (cross_route d hv f g s t i j h hi hj hc)

/-- Every placed nine-cluster has exactly nine lattice vertices. -/
theorem cluster_card (f : Frame) : (cluster f).card = 9 := by
  rw [Finset.card_image_of_injective _ f.injective]
  unfold NineClusterAttachment.points
  rw [Finset.card_image_of_injective _ NineCluster.point_injective]
  simp

theorem points_card (d : Drawing) (hv : d.Valid) (f g : Frame) (s t : Fin 4)
    (h : Between d f g s t) : (points d f g).card = 18 + 2 * d.halfSize := by
  rw [points, Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨h.2.2.1, h.2.1.symm⟩),
    Finset.card_union_of_disjoint h.1, cluster_card, cluster_card, d.card hv]
  omega

theorem corner_color (f : Frame) (i j : Fin 4) : color (corner f i) = color (corner f j) := by
  apply (f.color_eq_iff _ _).mpr
  fin_cases i <;> fin_cases j <;> decide

/-- The two attachment edges flip both endpoint colors, so the tentacle's
cross-route parity is precisely the parity of the exterior cluster corners. -/
theorem Between.cross_color_iff {d : Drawing} {f g : Frame} {s t : Fin 4}
    (h : Between d f g s t) (i j : Fin 4) :
    color (d.start 0) ≠ color (d.tip 0) ↔ color (corner f i) ≠ color (corner g j) := by
  have ha := adjacent_color_ne h.start_adjacent
  have hb := adjacent_color_ne h.tip_adjacent
  rw [← corner_color f i s] at ha
  rw [← corner_color g j t] at hb
  have h0 := color_bounds (d.start 0)
  have h1 := color_bounds (d.tip 0)
  have h2 := color_bounds (corner f i)
  have h3 := color_bounds (corner g j)
  omega

/-- Exact endpoint-parity characterization for the assembled three regions. -/
theorem cross_route_iff (d : Drawing) (hv : d.Valid) (f g : Frame) (s t i j : Fin 4)
    (h : Between d f g s t) (hi : i ≠ s) (hj : t ≠ j) :
    HasRoute (points d f g) (corner f i) (corner g j) ↔
      color (corner f i) ≠ color (corner g j) := by
  constructor
  · intro hp
    exact route_opposite_color hp ⟨9 + d.halfSize, by rw [points_card d hv f g s t h]; omega⟩
  · intro hc
    exact cross_route d hv f g s t i j h hi hj ((h.cross_color_iff i j).mpr hc)

theorem cross_hamiltonian_iff (d : Drawing) (hv : d.Valid) (f g : Frame) (s t i j : Fin 4)
    (h : Between d f g s t) (hi : i ≠ s) (hj : t ≠ j) :
    (∃ p : (finiteGrid (points d f g)).Walk
      ⟨corner f i, left_corner_mem d f g i⟩ ⟨corner g j, right_corner_mem d f g j⟩,
      p.IsHamiltonian) ↔ color (corner f i) ≠ color (corner g j) := by
  rw [← hasRoute_iff_hamiltonian]
  exact cross_route_iff d hv f g s t i j h hi hj

end GridHardness.TwoClusterAssembly
