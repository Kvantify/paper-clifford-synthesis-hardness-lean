/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunsReverse
public import GridHardness.SatCollarCorridorCore
public import GridHardness.SatNineClusterPlacement

/-!
# SAT Collar Corridors

The radius-sixteen central corridors, oriented from the color-zero owner to
the nonowning endpoint, and their computed maximal straight runs. Every run
has at least thirty-two unit steps; consecutive runs turn perpendicularly.
-/

@[expose] public section

namespace GridHardness.SatCollarCorridors
open CliffordComplexity CliffordSynthesis LatticeRouteDirections LatticeRouteRuns
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Vertex := SatBipartiteDrawing.Vertex
abbrev Edge := SatBipartiteDrawing.Edge

/-- Reverse an edge precisely when its catalogue source does not own it. -/
def reverseEdge (x : SatTy.denote) (e : Edge x) : Bool :=
  !(SatNineClusterPlacement.ownsTentacles x (SatBipartiteDrawing.source x e))

def startVertex (x : SatTy.denote) (e : Edge x) : Vertex x :=
  SatBipartiteDirections.endpointVertex x e (reverseEdge x e)

def endVertex (x : SatTy.denote) (e : Edge x) : Vertex x :=
  SatBipartiteDirections.endpointVertex x e (!(reverseEdge x e))

theorem owners (x : SatTy.denote) (e : Edge x) :
    SatNineClusterPlacement.ownsTentacles x (startVertex x e)=true ∧
      SatNineClusterPlacement.ownsTentacles x (endVertex x e)=false := by
  have h := SatNineClusterPlacement.opposite_owners x _ _ (SatBipartiteEdges.edge_adj x e)
  unfold startVertex endVertex SatBipartiteDirections.endpointVertex reverseEdge
  cases hs : SatNineClusterPlacement.ownsTentacles x (SatBipartiteDrawing.source x e) <;>
    cases ht : SatNineClusterPlacement.ownsTentacles x (SatBipartiteDrawing.target x e) <;>
    simp_all

theorem endpoints_adj (x : SatTy.denote) (e : Edge x) :
    (SatBipartiteDrawing.graph x).Adj (startVertex x e) (endVertex x e) := by
  unfold startVertex endVertex
  cases h : reverseEdge x e
  · exact SatBipartiteEdges.edge_adj x e
  · exact (SatBipartiteEdges.edge_adj x e).symm

theorem endpoints_ne (x : SatTy.denote) (e : Edge x) : startVertex x e≠endVertex x e := by
  intro he
  have h := owners x e
  rw [he,h.2] at h
  simp at h

noncomputable def startPoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) : Point := SatCollarCorridorCore.endpoint x hw e (reverseEdge x e)

noncomputable def endPoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) : Point := SatCollarCorridorCore.endpoint x hw e (!(reverseEdge x e))

noncomputable def route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) : List Point :=
  orient (SatCollarCorridorCore.route x hw e) (reverseEdge x e)

noncomputable def runs (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) : List Run := compress (route x hw e)

/-- Changing the orientation preserves the corridor's underlying points. -/
theorem mem_route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (q : Point) : q∈route x hw e ↔ q∈SatCollarCorridorCore.route x hw e :=
  mem_orient _ _ _

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (route x hw e).head?=some (startPoint x hw e) ∧
    (route x hw e).getLast?=some (endPoint x hw e) ∧
    (route x hw e).Nodup ∧ (route x hw e).IsChain UnitStep ∧
    33≤(route x hw e).length ∧ (route x hw e).length≤6291456*(x.length+1) := by
  have h := SatCollarCorridorCore.route_certificate x hw e
  refine ⟨?_,?_,orient_nodup _ _ h.2.2.1,orient_chain _ _ h.2.2.2.1,?_,?_⟩
  · unfold route startPoint
    cases he : reverseEdge x e
    · exact h.1
    · simpa [orient] using h.2.1
  · unfold route endPoint
    cases he : reverseEdge x e
    · exact h.2.1
    · simpa [orient] using h.1
  · simpa only [route,orient_length] using h.2.2.2.2.1
  · simpa only [route,orient_length] using h.2.2.2.2.2

/-- Every computed run of the owner-oriented corridor is long enough for
local width-two turn and attachment constructions. -/
theorem runs_long (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ∀ r∈runs x hw e,32≤r.2 := by
  apply runs_orient_lower (SatCollarCorridorCore.route x hw e)
    (SatCollarCorridorCore.route_certificate x hw e).2.2.2.1 32 _ (reverseEdge x e)
  exact core_runs_long 64 16 16 (by decide) (SatBipartiteDrawing.route x hw e)
    (SatBipartiteDrawing.route_certificate x hw e).2.2.2.1

theorem runs_turns (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ((runs x hw e).map Prod.fst).IsChain (fun d f => d.val%2≠f.val%2) :=
  runs_perpendicular (route x hw e) (route_certificate x hw e).2.2.1
    (route_certificate x hw e).2.2.2.1

/-- Expansion of the computed runs reproduces the actual oriented
corridor point for point, including the correctly selected owner endpoint. -/
theorem runs_reconstruct (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    expandRuns (startPoint x hw e) (runs x hw e)=route x hw e := by
  have hc := route_certificate x hw e
  unfold runs
  cases he : route x hw e with
  | nil => simp [he] at hc
  | cons p l =>
    have hp : p=startPoint x hw e := by simpa [he] using hc.1
    subst p
    exact expandRuns_compress _ l (by simpa [he] using hc.2.2.2.1)

theorem runs_nonempty (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    runs x hw e≠[] := compress_ne_nil _ (by have := (route_certificate x hw e).2.2.2.2.1; omega)

theorem runs_total_steps (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ((runs x hw e).map Prod.snd).sum=(route x hw e).length-1 := run_step_count _

theorem runs_count_bound (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (runs x hw e).length≤6291456*(x.length+1) := by
  have h := run_count_le (route x hw e)
  have hc := (route_certificate x hw e).2.2.2.2.2
  change (compress (route x hw e)).length≤_
  omega

/-- Orientation preserves the established thirty-two-step separation between
different central corridors. -/
theorem pairwise_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f) :
    32≤IntegerGrid.manhattan p q :=
  SatCollarCorridorCore.pairwise_distance x hw e f hef p q
    ((mem_route x hw e p).mp hp) ((mem_route x hw f q).mp hq)

end GridHardness.SatCollarCorridors
