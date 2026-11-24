/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteCorridors
public import GridHardness.LatticeRouteCoreSeparation

/-!
# SAT Bipartite Corridor Separation

Distinct external corridor cores have a sixteen-step gap, including
when their graph edges share an endpoint. Original graph-edge uniqueness
limits route intersections to at most one original vertex; removing eight
steps around that vertex creates the required corridor margin.
-/

public section

namespace GridHardness.SatBipartiteCorridors
open CliffordComplexity CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem endpoint_pairs_eq {V : Type*} (a b c d p q : V) (hpq : p ≠q)
    (hpa : p =a ∨ p =b) (hqa : q =a ∨ q =b)
    (hpc : p =c ∨ p =d) (hqc : q =c ∨ q =d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  rcases hpa with hpa | hpa <;> rcases hqa with hqa | hqa <;>
    rcases hpc with hpc | hpc <;> rcases hqc with hqc | hqc <;> aesop

/-- Two distinct actual graph edges have at most one common point in
the original simultaneous lattice drawing. -/
theorem original_shared_point_unique (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : SatBipartiteDrawing.Edge x) (hef : e ≠f) (p q : Point)
    (hpe : p ∈SatBipartiteDrawing.route x hw e)
    (hpf : p ∈SatBipartiteDrawing.route x hw f)
    (hqe : q ∈SatBipartiteDrawing.route x hw e)
    (hqf : q ∈SatBipartiteDrawing.route x hw f) : p=q := by
  obtain ⟨v,hpv,hve,hvf⟩ := SatBipartiteDrawing.shared_vertex x hw e f hef p hpe hpf
  obtain ⟨w,hqw,hwe,hwf⟩ := SatBipartiteDrawing.shared_vertex x hw e f hef q hqe hqf
  by_cases hvw : v=w
  · exact hpv.trans ((congrArg (SatBipartiteDrawing.point x hw) hvw).trans hqw.symm)
  · exact False.elim (hef (SatBipartiteEdges.unordered_endpoints_injective x e f
      (endpoint_pairs_eq _ _ _ _ v w hvw hve hwe hvf hwf)))

/-- All distinct corridor cores are separated by at least sixteen grid
steps, even for edges meeting at a common endpoint. -/
theorem pairwise_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : SatBipartiteDrawing.Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f) :
    16≤IntegerGrid.manhattan p q := by
  apply LatticeRouteCore.subdivision_separation 64 8 (by decide) (by decide)
    (SatBipartiteDrawing.route x hw e) (SatBipartiteDrawing.route x hw f)
    (SatBipartiteDrawing.route_certificate x hw e).2.2.2.1
    (SatBipartiteDrawing.route_certificate x hw f).2.2.2.1
    (original_shared_point_unique x hw e f hef) p q
    (mem_subdivide x hw e p hp) (mem_subdivide x hw f q hq)
  · intro z hze hzf
    obtain ⟨v,rfl,_,_⟩ := SatBipartiteDrawing.shared_vertex x hw e f hef z hze hzf
    exact anchor_clearance x hw e v p hp
  · intro z hze hzf
    obtain ⟨v,rfl,_,_⟩ := SatBipartiteDrawing.shared_vertex x hw e f hef z hze hzf
    exact anchor_clearance x hw f v q hq

/-- Two-unit neighborhoods of different cores retain a twelve-step
margin. Applications must show that their strips lie in these neighborhoods. -/
theorem neighborhood_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : SatBipartiteDrawing.Edge x) (hef : e ≠f) (p q u v : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f)
    (hpu : IntegerGrid.manhattan p u ≤2) (hqv : IntegerGrid.manhattan q v ≤2) :
    12≤IntegerGrid.manhattan u v := by
  have hd := pairwise_distance x hw e f hef p q hp hq
  have ht1 := IntegerGrid.manhattan_triangle p u q
  have ht2 := IntegerGrid.manhattan_triangle u v q
  rw [IntegerGrid.manhattan_comm v q] at ht2
  omega

theorem pairwise_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : SatBipartiteDrawing.Edge x) (hef : e ≠f) :
    List.Disjoint (route x hw e) (route x hw f) := by
  intro p hp hq
  have hd := pairwise_distance x hw e f hef p p hp hq
  simp [IntegerGrid.manhattan] at hd

theorem pairwise_nonadjacent (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : SatBipartiteDrawing.Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f) :
    IntegerGrid.manhattan p q≠1 := by
  have hd := pairwise_distance x hw e f hef p q hp hq
  omega

end GridHardness.SatBipartiteCorridors
