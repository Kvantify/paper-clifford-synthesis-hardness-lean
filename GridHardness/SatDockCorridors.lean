/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteAsymmetricCore
public import GridHardness.SatCollarRunClearance
public import GridHardness.NineClusterDockGeometry

/-!
# SAT Dock Corridors

Owner-oriented routes with the actual joining cuts: two steps at the
owner and eight, nine or ten at the recipient, according to its side.
The construction handles single-run edges without a separate case.
-/

@[expose] public section

namespace GridHardness.SatDockCorridors
open CliffordComplexity CliffordSynthesis LatticeRouteDirections LatticeRouteRuns
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Vertex := SatBipartiteDrawing.Vertex
abbrev Edge := SatBipartiteDrawing.Edge
abbrev owner := SatCollarCorridors.startVertex
abbrev recipient := SatCollarCorridors.endVertex
abbrev reverseEdge := SatCollarCorridors.reverseEdge

def endpointVertex (x : SatTy.denote) (e : Edge x) (b : Bool) : Vertex x :=
  if b then recipient x e else owner x e

noncomputable def original (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : List Point :=
  orient (SatBipartiteDrawing.route x hw e) (reverseEdge x e)

theorem original_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (original x hw e).Nodup ∧ (original x hw e).IsChain UnitStep ∧
    2≤(original x hw e).length ∧ (original x hw e).length≤98304*(x.length+1) := by
  have h := SatBipartiteDrawing.route_certificate x hw e
  exact ⟨orient_nodup _ _ h.2.2.1,orient_chain _ _ h.2.2.2.1,
    by simpa only [original,orient_length] using h.2.2.2.2.1,
    by simpa only [original,orient_length] using h.2.2.2.2.2⟩

noncomputable def direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (b : Bool) : Fin 4 :=
  SatBipartiteDirections.direction x hw e (if b then !(reverseEdge x e) else reverseEdge x e)

noncomputable def side (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (b : Bool) : Fin 4 :=
  NineClusterDockGeometry.sideOfDirection (direction x hw e b)

theorem original_endpoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (b : Bool) :
    endpointPoint (original x hw e) b (original_certificate x hw e).2.2.1=
      SatBipartiteDrawing.point x hw (endpointVertex x e b) := by
  have h := SatBipartiteDirections.endpointPoint_eq x hw e
    (if b then !(reverseEdge x e) else reverseEdge x e)
  cases hr : reverseEdge x e <;> cases b <;>
    simpa [original,endpointVertex,owner,recipient,SatCollarCorridors.startVertex,
      SatCollarCorridors.endVertex,hr,endpointPoint,orient] using h

theorem original_direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (b : Bool) :
    tangent (original x hw e) b (original_certificate x hw e).2.2.1=direction x hw e b := by
  cases hr : reverseEdge x e <;> cases b <;>
    simp [original,direction,SatBipartiteDirections.direction,tangent,endpointPoint,neighborPoint,orient,hr]

noncomputable def endCut (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Nat :=
  ![8,9,10,9] (side x hw e true)

theorem endCut_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    8≤endCut x hw e ∧ endCut x hw e≤10 := by
  unfold endCut
  generalize side x hw e true=s
  fin_cases s <;> decide

noncomputable def pointAt (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (b : Bool) (k : Nat) : Point :=
  let p := SatNineClusterPlacement.anchor x hw (endpointVertex x e b)
  let r := DirectedLocalLayout.ray (direction x hw e b) k
  (p.1+r.1,p.2+r.2)

noncomputable def startPoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Point :=
  pointAt x hw e false 2

noncomputable def endPoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Point :=
  pointAt x hw e true (endCut x hw e)

noncomputable def route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : List Point :=
  LatticeRouteCore.core 64 2 (endCut x hw e) (original x hw e)

theorem interpolate_endpoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (b : Bool) (k : Nat) :
    LatticeSubdivision.interpolate 64
      (endpointPoint (original x hw e) b (original_certificate x hw e).2.2.1)
      (neighborPoint (original x hw e) b (original_certificate x hw e).2.2.1) k=pointAt x hw e b k := by
  rw [tangent_spec _ _ _ (original_certificate x hw e).2.1,original_endpoint,original_direction]
  dsimp [pointAt,SatNineClusterPlacement.anchor]
  generalize SatBipartiteDrawing.point x hw (endpointVertex x e b)=p
  generalize direction x hw e b=d
  fin_cases d <;> simp [LatticeSubdivision.interpolate,LatticeSubdivision.scale,step,DirectedLocalLayout.ray]

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (route x hw e).head?=some (startPoint x hw e) ∧
    (route x hw e).getLast?=some (endPoint x hw e) ∧
    (route x hw e).Nodup ∧ (route x hw e).IsChain UnitStep ∧
    53≤(route x hw e).length ∧ (route x hw e).length≤6291456*(x.length+1) := by
  have hb := endCut_bounds x hw e
  have h := original_certificate x hw e
  have hc := LatticeRouteCore.certificate 64 2 (endCut x hw e) (by decide) (by omega)
    _ h.1 h.2.1 h.2.2.1
  rw [interpolate_endpoint,interpolate_endpoint] at hc
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,?_,?_⟩ <;>
    change _ at hc <;> dsimp only [route] <;> omega

theorem route_direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (b : Bool) :
    tangent (route x hw e) b (by have := (route_certificate x hw e).2.2.2.2.1; omega)=
      direction x hw e b := by
  have hb := endCut_bounds x hw e
  have h := original_certificate x hw e
  change tangent (LatticeRouteCore.core 64 2 (endCut x hw e) (original x hw e)) b _ = _
  rw [LatticeRouteCore.tangent_eq 64 2 (endCut x hw e) (by decide) (by omega)
    _ h.1 h.2.1 h.2.2.1 b,original_direction]

noncomputable def runs (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : List Run :=
  compress (route x hw e)

theorem runs_long (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ∀ r∈runs x hw e,52≤r.2 := by
  have hb := endCut_bounds x hw e
  have h := core_runs_long 64 2 (endCut x hw e) (by decide) (original x hw e)
    (original_certificate x hw e).2.1
  intro r hr
  have hh := h r hr
  omega

theorem runs_turns (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ((runs x hw e).map Prod.fst).IsChain (fun d f => d.val%2≠f.val%2) :=
  runs_perpendicular _ (route_certificate x hw e).2.2.1 (route_certificate x hw e).2.2.2.1

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

theorem indexSeparated (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteCore.IndexSeparated 64 (route x hw e) := by
  have h := original_certificate x hw e
  exact LatticeRouteCore.core_indexSeparated 64 2 (endCut x hw e) (by decide) _ h.1 h.2.1 h.2.2.1

theorem start_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (owner x e)) (startPoint x hw e)=2 := by
  dsimp [startPoint,pointAt,endpointVertex]
  generalize direction x hw e false=d
  fin_cases d <;> simp [DirectedLocalLayout.ray,IntegerGrid.manhattan]

theorem end_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (recipient x e)) (endPoint x hw e)=endCut x hw e := by
  dsimp [endPoint,pointAt,endpointVertex]
  generalize direction x hw e true=d
  fin_cases d <;> simp [DirectedLocalLayout.ray,IntegerGrid.manhattan]

end GridHardness.SatDockCorridors
