/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireSeparation
public import GridHardness.CorrectedSatIntervalPermutationCoreEdges

/-!
# SAT Clause Drawing

A simultaneous drawing of all clause bodies and the backbone edges
between consecutive clauses. The remaining edges to occurrence wires,
variables and sentinels are outside this family.
-/

@[expose] public section

namespace GridHardness.SatClauseDrawing
open CliffordSynthesis PlanarSatAssembly
set_option autoImplicit false

abbrev Point := Int × Int
abbrev Vertex (m : Nat) := Fin m × Fin 12

inductive Edge (m : Nat) where
  | internal (c : Fin m) (e : Fin 14)
  | backbone (c d : Fin m) (consecutive : d.val=c.val+1)

def endpoints {m : Nat} : Edge m → Vertex m × Vertex m
  | .internal c e =>
    ((c,(PlanarSatClause.Lattice.edge e).1),(c,(PlanarSatClause.Lattice.edge e).2))
  | .backbone c d _ => ((c,1),(d,8))

def point {m : Nat} (v : Vertex m) : Point := SatClauseOrder.point v.1 v.2

def route {m : Nat} : Edge m → List Point
  | .internal c e => SatClauseOrder.route c e
  | .backbone c _ _ => SatClauseBackbone.route c

theorem point_injective (m : Nat) : Function.Injective (point (m:=m)) :=
  SatClauseOrder.point_injective m

theorem route_certificate {m : Nat} (e : Edge m) :
    (route e).head?=some (point (endpoints e).1) ∧
    (route e).getLast?=some (point (endpoints e).2) ∧
    (route e).Nodup ∧ (route e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2≤(route e).length ∧ (route e).length≤1073 := by
  cases e with
  | internal c e => exact SatClausePlacement.route_certificate (Fin.rev c) e
  | backbone c d h =>
    obtain ⟨hh,ht⟩ := SatClauseBackbone.route_endpoints c d h
    obtain ⟨hn,hs⟩ := SatClauseBackbone.route_simple c
    refine ⟨hh,ht,hn,hs,?_,?_⟩
    · change 2≤(SatClauseBackbone.route c).length
      rw [SatClauseBackbone.route_length]
      omega
    · change (SatClauseBackbone.route c).length≤1073
      rw [SatClauseBackbone.route_length]
      omega

theorem route_bounds {m : Nat} (e : Edge m) (q : Point) (hq : q ∈route e) :
    -104≤q.1 ∧ q.1≤-64 ∧ 0≤q.2 ∧ q.2≤3072*m+516 := by
  cases e with
  | internal c e =>
    exact SatClauseOrder.coordinates_bounded c q (SatClauseOrder.route_in_box c e q hq)
  | backbone c d h =>
    have hb := SatClauseBackbone.coordinates_bounded c q hq
    omega

theorem route_vertex_clear {m : Nat} (e : Edge m) (v : Vertex m) :
    point v∈route e ↔ v=(endpoints e).1 ∨ v=(endpoints e).2 := by
  rcases v with ⟨d,w⟩
  cases e with
  | internal c e =>
    by_cases hcd : d=c
    · subst d
      change SatClausePlacement.point (Fin.rev c) w∈
        SatClausePlacement.route (Fin.rev c) e ↔
        (c,w)=(c,(PlanarSatClause.Lattice.edge e).1) ∨
        (c,w)=(c,(PlanarSatClause.Lattice.edge e).2)
      rw [SatClausePlacement.route_vertex_clear]
      simp only [Prod.mk.injEq,true_and]
    · constructor
      · intro hm
        have hs := SatClauseOrder.boxes_separated d c hcd _ _
          (SatClauseOrder.point_in_box d w)
          (SatClauseOrder.route_in_box c e _ hm)
        simp [point,IntegerGrid.manhattan] at hs
      · intro he
        rcases he with he | he <;> exact False.elim (hcd (congrArg Prod.fst he))
  | backbone c b hcb =>
    constructor
    · intro hm
      rcases SatClauseBackbone.box_intersection c b d hcb _ hm
        (SatClauseOrder.point_in_box d w) with hc | hb
      · left
        exact point_injective m hc.2
      · right
        exact point_injective m hb.2
    · intro he
      rcases he with he | he
      · exact he ▸ (SatClauseBackbone.endpoint_mem c b hcb).1
      · exact he ▸ (SatClauseBackbone.endpoint_mem c b hcb).2

private theorem endpoint_of_mem {m : Nat} (e : Edge m) (v : Vertex m)
    (q : Point) (hq : q ∈route e) (hv : q =point v) :
    q=point (endpoints e).1 ∨ q=point (endpoints e).2 := by
  rw [hv] at hq
  exact ((route_vertex_clear e v).mp hq).imp
    (fun h => hv.trans (congrArg point h)) (fun h => hv.trans (congrArg point h))

/-- Any two distinct edges meet only at an endpoint of each edge. -/
theorem route_intersection {m : Nat} (e f : Edge m) (hef : e ≠f)
    (q : Point) (he : q ∈route e) (hf : q ∈route f) :
    (q=point (endpoints e).1 ∨ q=point (endpoints e).2) ∧
    (q=point (endpoints f).1 ∨ q=point (endpoints f).2) := by
  cases e with
  | internal c a =>
    cases f with
    | internal d b =>
      by_cases hcd : c=d
      · subst d
        have hab : a≠b := fun h => hef (by cases h; rfl)
        exact SatClausePlacement.route_intersection (Fin.rev c) a b hab q he hf
      · have hs := SatClauseOrder.boxes_separated c d hcd q q
          (SatClauseOrder.route_in_box c a q he)
          (SatClauseOrder.route_in_box d b q hf)
        simp [IntegerGrid.manhattan] at hs
    | backbone d b hdb =>
      have hi := (SatClauseBackbone.internal_route_intersection d b c hdb a q).mp ⟨hf,he⟩
      rcases hi with ⟨_,hq,_⟩ | ⟨_,hq,_⟩
      · exact ⟨endpoint_of_mem (.internal c a) (d,1) q he hq,Or.inl hq⟩
      · exact ⟨endpoint_of_mem (.internal c a) (b,8) q he hq,Or.inr hq⟩
  | backbone c d hcd =>
    cases f with
    | internal b a =>
      have hi := (SatClauseBackbone.internal_route_intersection c d b hcd a q).mp ⟨he,hf⟩
      rcases hi with ⟨_,hq,_⟩ | ⟨_,hq,_⟩
      · exact ⟨Or.inl hq,endpoint_of_mem (.internal b a) (c,1) q hf hq⟩
      · exact ⟨Or.inr hq,endpoint_of_mem (.internal b a) (d,8) q hf hq⟩
    | backbone a b hab =>
      have hca : c≠a := by
        intro h
        subst a
        have hdb : d=b := Fin.ext (by omega)
        subst b
        exact hef rfl
      have hs := SatClauseBackbone.routes_separated c a hca q q he hf
      simp [IntegerGrid.manhattan] at hs

theorem wire_separation {n m : Nat} (φ : Formula n m) (e : Edge m) (q r : Point)
    (hq : q ∈route e) (hr : SatClauseWireSeparation.WirePoint (SatClauseOrder.permutation φ) r) :
    64≤IntegerGrid.manhattan q r := by
  cases e with
  | internal c e => exact SatClauseWireSeparation.internal_route_separation φ c e q r hq hr
  | backbone c d h => exact SatClauseWireSeparation.backbone_separation φ c q r hq hr

noncomputable def vertex {n m : Nat} (φ : Formula n m) (v : Vertex m) :
    (SatClauseOrder.graph φ).Vertex := SatClauseOrder.vertex φ v.1 v.2

theorem vertex_injective {n m : Nat} (φ : Formula n m) :
    Function.Injective (vertex φ) := SatClauseOrder.vertex_injective φ

/-- Every drawn edge is an edge of the actual completed sweep graph. -/
theorem edge_is_arc {n m : Nat} (φ : Formula n m) (e : Edge m) :
    (SatClauseOrder.graph φ).adj (vertex φ (endpoints e).1) (vertex φ (endpoints e).2) := by
  cases e with
  | internal c e =>
    exact (CorrectedSatInterval.PermutationGraph.CoreEdges.clause_internal_iff
      φ (SatClauseOrder.permutation φ) c _ _).mpr (PlanarSatClause.Lattice.edge_body e)
  | backbone c d h =>
    exact (CorrectedSatInterval.PermutationGraph.CoreEdges.clause_backbone_iff
      φ (SatClauseOrder.permutation φ) c d).mpr h

/-- This family contains exactly the induced clause-vertex subgraph:
all fourteen internal arcs in each clause and all consecutive-clause links.
It does not omit or add any edge between these vertices. -/
theorem adj_iff {n m : Nat} (φ : Formula n m) (u v : Vertex m) :
    (SatClauseOrder.graph φ).adj (vertex φ u) (vertex φ v) ↔
      ∃ e : Edge m, endpoints e=(u,v) := by
  constructor
  · rcases u with ⟨c,a⟩
    rcases v with ⟨d,b⟩
    intro h
    have hh := (CorrectedSatInterval.PermutationGraph.CoreEdges.clause_adj_iff
      φ (SatClauseOrder.permutation φ) c d a b).mp h
    rcases hh with ⟨rfl,he⟩ | ⟨hcd,rfl,rfl⟩
    · obtain ⟨e,he⟩ := (PlanarSatClause.Lattice.body_iff_edge a b).mp he
      refine ⟨.internal c e,?_⟩
      simp only [endpoints,he]
    · exact ⟨.backbone c d hcd,rfl⟩
  · rintro ⟨e,he⟩
    have hs := edge_is_arc φ e
    simpa only [he] using hs

theorem same_point_iff_same_vertex {n m : Nat} (φ : Formula n m) (u v : Vertex m) :
    point u=point v ↔ vertex φ u=vertex φ v :=
  SatClauseOrder.same_point_iff_same_vertex φ u.1 v.1 u.2 v.2

end GridHardness.SatClauseDrawing
