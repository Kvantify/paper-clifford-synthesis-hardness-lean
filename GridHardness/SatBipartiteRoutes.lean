/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatScaledDrawing
public import GridHardness.LatticeRouteTrim

/-!
# SAT Bipartite Routes

External paths for the four-vertex bipartite replacement. Subdivision
provides sixteen steps per original edge; removing zero or three steps at
each end moves the attachment to the chosen gadget port.
-/

@[expose] public section

namespace GridHardness.SatBipartiteRoutes
open CliffordComplexity CliffordSynthesis DirectedLocalLayout LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Arc := SatCompleteDrawing.Arc

noncomputable def radius (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (b : Bool) : Nat :=
  SatBipartitePlacement.portRadius x hw (SatCompleteDrawing.endpointVertex x a b) b

theorem radius_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) (b : Bool) :
    radius x hw a b≤3 := SatBipartitePlacement.portRadius_le x hw _ b

noncomputable def route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) : List Point :=
  LatticeRouteTrim.trim (radius x hw a false) (radius x hw a true) (SatScaledDrawing.route x a)

theorem endpointPoint_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) (b : Bool) :
    LatticeRouteDirections.endpointPoint (SatCompleteDrawing.route x a) b
      (by have := SatCompleteDrawing.route_length_lower x a; omega)=
      SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b) := by
  have h := LatticeRouteDirections.endpointPoint_spec (SatCompleteDrawing.route x a) b
    (by have := SatCompleteDrawing.route_length_lower x a; omega)
  have hc := SatCompleteDrawing.route_certificate x hw a
  cases b
  · exact Option.some.inj (h.symm.trans hc.1)
  · exact Option.some.inj (h.symm.trans hc.2.1)

theorem endpoint_interpolate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (b : Bool) :
    interpolate 16
      (LatticeRouteDirections.endpointPoint (SatCompleteDrawing.route x a) b
        (by have := SatCompleteDrawing.route_length_lower x a; omega))
      (LatticeRouteDirections.neighborPoint (SatCompleteDrawing.route x a) b
        (by have := SatCompleteDrawing.route_length_lower x a; omega)) (radius x hw a b)=
      SatBipartitePlacement.point x hw
        (SatCompleteDrawing.endpointVertex x a b,SatBipartitePlacement.portIndex b) := by
  rw [endpointPoint_eq x hw,SatCompleteDrawing.direction_spec x hw,SatBipartitePlacement.port_point x hw]
  generalize SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b)=p
  generalize SatCompleteDrawing.direction x a b=d
  change interpolate 16 p (LatticeRouteDirections.step p d) (radius x hw a b)=
    ((DirectedScaledLayout.anchor p).1+(ray d (radius x hw a b)).1,
     (DirectedScaledLayout.anchor p).2+(ray d (radius x hw a b)).2)
  fin_cases d <;> simp [interpolate,LatticeRouteDirections.step,ray,DirectedScaledLayout.anchor]

theorem initial_port (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    (SatScaledDrawing.route x a)[radius x hw a false]'
      (by have := radius_le x hw a false; have := SatScaledDrawing.route_length_lower x a; omega)=
      SatBipartitePlacement.point x hw (SatCompleteDrawing.source x a,3) := by
  have hr := radius_le x hw a false
  unfold SatScaledDrawing.route
  rw [subdivide_getElem_initial 16 _
    (by have := SatCompleteDrawing.route_length_lower x a; omega) _ (by omega)]
  exact endpoint_interpolate x hw a false

theorem terminal_port (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    (SatScaledDrawing.route x a)[(SatScaledDrawing.route x a).length-1-radius x hw a true]'
      (by have := radius_le x hw a true; have := SatScaledDrawing.route_length_lower x a; omega)=
      SatBipartitePlacement.point x hw (SatCompleteDrawing.target x a,0) := by
  have hr := radius_le x hw a true
  unfold SatScaledDrawing.route
  rw [subdivide_getElem_terminal 16 (by decide) _
    (by have := SatCompleteDrawing.route_length_lower x a; omega) _ (by omega)]
  simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.neighborPoint,
    LatticeRouteDirections.orient,Nat.sub_sub,SatCompleteDrawing.endpointVertex,
    SatBipartitePlacement.portIndex] using endpoint_interpolate x hw a true

/-- The path runs between the actual source's outgoing endpoint and the
actual target's incoming endpoint. It still has at least twenty-seven points. -/
theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    (route x hw a).head?=some (SatBipartitePlacement.point x hw (SatCompleteDrawing.source x a,3)) ∧
    (route x hw a).getLast?=some (SatBipartitePlacement.point x hw (SatCompleteDrawing.target x a,0)) ∧
    (route x hw a).Nodup ∧ (route x hw a).IsChain UnitStep ∧
    27≤(route x hw a).length ∧ (route x hw a).length≤98304*(x.length+1) := by
  have hs := radius_le x hw a false
  have ht := radius_le x hw a true
  have hl := SatScaledDrawing.route_length_lower x a
  have hc := SatScaledDrawing.route_certificate x hw a
  have hpos : radius x hw a false+radius x hw a true<(SatScaledDrawing.route x a).length := by omega
  refine ⟨?_,?_,LatticeRouteTrim.nodup _ _ _ hc.2.2.1,
    LatticeRouteTrim.chain _ _ _ hc.2.2.2.1,?_,?_⟩
  · rw [route,LatticeRouteTrim.head _ _ _ hpos,initial_port]
  · rw [route,LatticeRouteTrim.getLast _ _ _ hpos,terminal_port]
  · change 27≤(LatticeRouteTrim.trim _ _ _).length
    rw [LatticeRouteTrim.length]
    omega
  · have hb := hc.2.2.2.2
    change (LatticeRouteTrim.trim _ _ _).length≤_
    rw [LatticeRouteTrim.length]
    omega

theorem mem_scaled (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x)
    (q : Point) (hq : q ∈route x hw a) : q∈SatScaledDrawing.route x a :=
  LatticeRouteTrim.mem _ _ _ q hq

theorem unrelated_gadget_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (v : SatCompleteDrawing.Vertex x)
    (hs : v ≠SatCompleteDrawing.source x a) (ht : v ≠SatCompleteDrawing.target x a)
    (i : Fin 4) (q : Point) (hq : q ∈route x hw a) :
    13≤IntegerGrid.manhattan q (SatBipartitePlacement.point x hw (v,i)) :=
  SatScaledDrawing.unrelated_gadget_distance x hw a v hs ht i q (mem_scaled x hw a q hq)

end GridHardness.SatBipartiteRoutes
