/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteDirections
public import GridHardness.LatticeRouteCore

/-!
# SAT Bipartite Corridors

Central corridors of the complete bipartite drawing. Dilation by
sixty-four and removal of eight points at each end reserve local vertex
neighborhoods for cluster docks. These are centerline paths; their later
width-two thickening is a separate construction.
-/

@[expose] public section

namespace GridHardness.SatBipartiteCorridors
open CliffordComplexity CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatBipartiteDrawing.Vertex
abbrev Edge := SatBipartiteDrawing.Edge

noncomputable def anchor (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) : Point :=
  scale 64 (SatBipartiteDrawing.point x hw v)

noncomputable def route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : List Point :=
  LatticeRouteCore.core 64 8 8 (SatBipartiteDrawing.route x hw e)

noncomputable def endpoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) : Point :=
  let p := anchor x hw (SatBipartiteDirections.endpointVertex x e b)
  let r := DirectedLocalLayout.ray (SatBipartiteDirections.direction x hw e b) 8
  (p.1+r.1,p.2+r.2)

theorem endpoint_interpolate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    interpolate 64
      (LatticeRouteDirections.endpointPoint (SatBipartiteDrawing.route x hw e) b
        (SatBipartiteDrawing.route_certificate x hw e).2.2.2.2.1)
      (LatticeRouteDirections.neighborPoint (SatBipartiteDrawing.route x hw e) b
        (SatBipartiteDrawing.route_certificate x hw e).2.2.2.2.1) 8 = endpoint x hw e b := by
  rw [SatBipartiteDirections.endpointPoint_eq,SatBipartiteDirections.direction_spec]
  dsimp [endpoint,anchor]
  generalize SatBipartiteDrawing.point x hw (SatBipartiteDirections.endpointVertex x e b)=p
  generalize SatBipartiteDirections.direction x hw e b=d
  fin_cases d <;> simp [interpolate,scale,LatticeRouteDirections.step,DirectedLocalLayout.ray]

/-- The two central endpoints lie eight units along the original cardinal ports. -/
theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (route x hw e).head?=some (endpoint x hw e false) ∧
    (route x hw e).getLast?=some (endpoint x hw e true) ∧
    (route x hw e).Nodup ∧ (route x hw e).IsChain UnitStep ∧
    49≤(route x hw e).length ∧ (route x hw e).length≤6291456*(x.length+1) := by
  have hc := SatBipartiteDrawing.route_certificate x hw e
  have hn : SatBipartiteDrawing.route x hw e≠[] := by intro he; simp [he] at hc
  have hs := subdivide_length 64 (SatBipartiteDrawing.route x hw e) hn
  have hmin : 65≤(subdivide 64 (SatBipartiteDrawing.route x hw e)).length := by omega
  have hlen : (route x hw e).length=
      (subdivide 64 (SatBipartiteDrawing.route x hw e)).length-8-8 :=
    LatticeRouteTrim.length _ _ _
  refine ⟨?_,?_,?_,?_,by omega,?_⟩
  · rw [route,LatticeRouteCore.core,LatticeRouteTrim.head 8 8 _ (by omega),
      subdivide_getElem_initial 64 _ hc.2.2.2.2.1 8 (by decide)]
    exact congrArg some (endpoint_interpolate x hw e false)
  · rw [route,LatticeRouteCore.core,LatticeRouteTrim.getLast 8 8 _ (by omega),
      subdivide_getElem_terminal 64 (by decide) _ hc.2.2.2.2.1 8 (by decide)]
    apply congrArg some
    simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.neighborPoint,
      LatticeRouteDirections.orient,Nat.sub_sub] using endpoint_interpolate x hw e true
  · exact LatticeRouteTrim.nodup 8 8 _ (subdivide_nodup 64 _ hc.2.2.1 hc.2.2.2.1)
  · exact LatticeRouteTrim.chain 8 8 _ (subdivide_chain 64 (by decide) _ hc.2.2.2.1)
  · have hu := subdivide_length_le 64 (by decide) (SatBipartiteDrawing.route x hw e)
    omega

theorem mem_subdivide (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (q : Point) (hq : q ∈route x hw e) :
    q∈subdivide 64 (SatBipartiteDrawing.route x hw e) :=
  LatticeRouteCore.mem_subdivide 64 8 8 _ q hq

/-- Every cluster anchor, including the two incident ones, is clear of the core. -/
theorem anchor_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) (q : Point) (hq : q ∈route x hw e) :
    8≤IntegerGrid.manhattan (anchor x hw v) q := by
  have hc := SatBipartiteDrawing.route_certificate x hw e
  by_cases hv : v=SatBipartiteDrawing.source x e
  · subst v
    have hh : (SatBipartiteDrawing.route x hw e)[0]'(by omega)=
        SatBipartiteDrawing.point x hw (SatBipartiteDrawing.source x e) := by
      exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans
        (List.head?_eq_getElem?.symm.trans hc.1))
    simpa only [anchor,hh] using LatticeRouteCore.initial_clearance 64 8 8 (by decide)
      (by decide) _ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 q hq
  · by_cases ht : v=SatBipartiteDrawing.target x e
    · subst v
      have hh : (SatBipartiteDrawing.route x hw e)[(SatBipartiteDrawing.route x hw e).length-1]'
          (by omega)=SatBipartiteDrawing.point x hw (SatBipartiteDrawing.target x e) := by
        exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans
          (List.getLast?_eq_getElem?.symm.trans hc.2.1))
      simpa only [anchor,hh] using LatticeRouteCore.terminal_clearance 64 8 8 (by decide)
        (by decide) _ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 q hq
    · have hn : SatBipartiteDrawing.point x hw v∉SatBipartiteDrawing.route x hw e := by
        rw [SatBipartiteDrawing.actual_vertex_clear]
        exact not_or.mpr ⟨hv,ht⟩
      have hs := LatticeRouteCore.unrelated_clearance 64 8 8 _ hc.2.2.2.1 _ hn q hq
      rw [IntegerGrid.manhattan_comm] at hs
      exact (by decide : 8≤64).trans hs

end GridHardness.SatBipartiteCorridors
