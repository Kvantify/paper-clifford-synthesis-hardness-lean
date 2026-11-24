/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteEdges
public import GridHardness.SatBipartiteRouteClearance
public import GridHardness.SatBipartiteRouteIntersection

/-!
# SAT Bipartite Drawing

The simultaneous orthogonal drawing after the four-vertex bipartite
replacement. The exact edge catalogue includes internal gadget paths and
the trimmed external routes. These paths describe a drawing of the source
graph; they do not replace optional graph edges by forced subdivisions in
a Hamiltonian-cycle reduction. A valid cluster/tentacle layout is separate.
-/

@[expose] public section

namespace GridHardness.SatBipartiteDrawing
open CliffordComplexity CliffordSynthesis
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Vertex := SatBipartiteEdges.Vertex
abbrev Edge := SatBipartiteEdges.Edge
abbrev graph := SatBipartiteEdges.graph
abbrev source := SatBipartiteEdges.source
abbrev target := SatBipartiteEdges.target
noncomputable abbrev point := SatBipartitePlacement.point

noncomputable def route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : Edge x → List Point
  | .inl (v,i) => [point x hw (v,i.castSucc),point x hw (v,i.succ)]
  | .inr a => SatBipartiteRoutes.route x hw a

noncomputable def Incident (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (q : Point) : Prop :=
  q=point x hw (source x e) ∨ q=point x hw (target x e)

theorem point_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    Function.Injective (point x hw) := SatBipartitePlacement.point_injective x hw

theorem endpoints_ne (x : SatTy.denote) (e : Edge x) : source x e≠target x e :=
  (SatBipartiteEdges.edge_adj x e).ne

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (route x hw e).head?=some (point x hw (source x e)) ∧
    (route x hw e).getLast?=some (point x hw (target x e)) ∧
    (route x hw e).Nodup ∧ (route x hw e).IsChain LatticeSubdivision.UnitStep ∧
    2≤(route x hw e).length ∧ (route x hw e).length≤98304*(x.length+1) := by
  cases e with
  | inl vi =>
    rcases vi with ⟨v,i⟩
    have hne : point x hw (v,i.castSucc)≠point x hw (v,i.succ) :=
      fun he => endpoints_ne x (.inl (v,i)) (point_injective x hw he)
    have hc : LatticeSubdivision.UnitStep (point x hw (v,i.castSucc)) (point x hw (v,i.succ)) :=
      (SatBipartitePlacement.local_adjacency x hw v i.castSucc i.succ).mpr (Or.inl rfl)
    refine ⟨rfl,rfl,?_,?_,by simp [route],?_⟩
    · simpa [route] using hne
    · simpa [route] using hc
    · simp only [route,List.length_cons,List.length_nil]
      omega
  | inr a =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatBipartiteRoutes.route_certificate x hw a
    exact ⟨hh,ht,hn,hc,(by decide : 2≤27).trans hl,hu⟩

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) :
    point x hw v∈route x hw e ↔ v=source x e ∨ v=target x e := by
  cases e with
  | inl vi =>
    rcases vi with ⟨u,i⟩
    simp only [route,List.mem_cons,List.not_mem_nil,or_false]
    exact or_congr (point_injective x hw).eq_iff (point_injective x hw).eq_iff
  | inr a => exact SatBipartiteRouteClearance.actual_vertex_clear x hw a v

theorem incident_of_vertex_mem (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) (hv : point x hw v ∈route x hw e) :
    Incident x hw e (point x hw v) :=
  ((actual_vertex_clear x hw e v).mp hv).elim
    (fun h => Or.inl (congrArg (point x hw) h)) (fun h => Or.inr (congrArg (point x hw) h))

theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (q : Point) (he : q ∈route x hw e) (hf : q ∈route x hw f) :
    Incident x hw e q ∧ Incident x hw f q := by
  cases e with
  | inl vi =>
    rcases vi with ⟨v,i⟩
    simp only [route,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact ⟨Or.inl rfl,incident_of_vertex_mem x hw f _ hf⟩
    · exact ⟨Or.inr rfl,incident_of_vertex_mem x hw f _ hf⟩
  | inr a =>
    cases f with
    | inl vi =>
      rcases vi with ⟨v,i⟩
      simp only [route,List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl | rfl
      · exact ⟨incident_of_vertex_mem x hw (.inr a) _ he,Or.inl rfl⟩
      · exact ⟨incident_of_vertex_mem x hw (.inr a) _ he,Or.inr rfl⟩
    | inr b =>
      exact SatBipartiteRoutes.route_intersection x hw a b (fun h => hef (congrArg Sum.inr h)) q he hf

theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (q : Point) (he : q ∈route x hw e) (hf : q ∈route x hw f) :
    ∃ v : Vertex x, q=point x hw v ∧
      (v=source x e ∨ v=target x e) ∧ (v=source x f ∨ v=target x f) := by
  obtain ⟨he,hf⟩ := route_intersection x hw e f hef q he hf
  rcases he with he | he
  · refine ⟨source x e,he,Or.inl rfl,?_⟩
    exact hf.elim (fun h => Or.inl (point_injective x hw (he.symm.trans h)))
      (fun h => Or.inr (point_injective x hw (he.symm.trans h)))
  · refine ⟨target x e,he,Or.inr rfl,?_⟩
    exact hf.elim (fun h => Or.inl (point_injective x hw (he.symm.trans h)))
      (fun h => Or.inr (point_injective x hw (he.symm.trans h)))

/-- All source graph edges, and only those edges, are drawn. -/
theorem adjacency_iff (x : SatTy.denote) (u v : Vertex x) :
    (graph x).Adj u v ↔ ∃ e : Edge x,
      (source x e=u ∧ target x e=v) ∨ (source x e=v ∧ target x e=u) :=
  SatBipartiteEdges.adjacency_iff x u v

/-- Every route stays in a rectangle whose side lengths are linear in
the number of clauses, including the small local gadget displacements. -/
theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (q : Point) (hq : q ∈route x hw e) :
    -2051≤q.1 ∧ q.1≤16*(SatVariableLattice.wireX (3*x.length)+128)+3 ∧
    -1027≤q.2 ∧ q.2≤16*SatExteriorLattice.top (3*x.length)+3 := by
  have hv (v : Vertex x) :
      -2051≤(point x hw v).1 ∧
      (point x hw v).1≤16*(SatVariableLattice.wireX (3*x.length)+128)+3 ∧
      -1027≤(point x hw v).2 ∧
      (point x hw v).2≤16*SatExteriorLattice.top (3*x.length)+3 := by
    have h := SatBipartitePlacement.point_bounds x hw v
    simp only [point]
    dsimp [SatExteriorLattice.top]
    omega
  cases e with
  | inl vi =>
    rcases vi with ⟨v,i⟩
    simp only [route,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact hv _
    · exact hv _
  | inr a =>
    have h := SatBipartiteRoutes.route_bounds x hw a q hq
    omega

end GridHardness.SatBipartiteDrawing
