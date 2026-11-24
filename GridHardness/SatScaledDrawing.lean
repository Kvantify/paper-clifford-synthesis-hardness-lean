/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteSeparation
public import GridHardness.SatBipartitePlacement

/-!
# SAT Scaled Drawing

The complete directed SAT routes after dilation by sixteen and
subdivision back into unit lattice steps. Unrelated four-vertex gadgets
have a thirteen-step margin from every point of these paths.
-/

@[expose] public section

namespace GridHardness.SatScaledDrawing
open CliffordComplexity PlanarSatAssembly CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Arc := SatCompleteDrawing.Arc
abbrev Vertex := SatCompleteDrawing.Vertex

noncomputable def point (x : SatTy.denote) (v : Vertex x) : Point :=
  scale 16 (SatCompleteDrawing.point x v)

noncomputable def route (x : SatTy.denote) (a : Arc x) : List Point :=
  subdivide 16 (SatCompleteDrawing.route x a)

theorem route_length (x : SatTy.denote) (a : Arc x) :
    (route x a).length=16*((SatCompleteDrawing.route x a).length-1)+1 :=
  subdivide_length 16 _ (by
    have h := SatCompleteDrawing.route_length_lower x a
    intro he
    rw [he] at h
    simp at h)

theorem route_length_lower (x : SatTy.denote) (a : Arc x) : 33≤(route x a).length := by
  have h := SatCompleteDrawing.route_length_lower x a
  rw [route_length]
  omega

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    (route x a).head?=some (point x (SatCompleteDrawing.source x a)) ∧
    (route x a).getLast?=some (point x (SatCompleteDrawing.target x a)) ∧
    (route x a).Nodup ∧ (route x a).IsChain UnitStep ∧
    (route x a).length≤98304*(x.length+1) := by
  obtain ⟨hh,ht,hn,hc,_,hl⟩ := SatCompleteDrawing.route_certificate x hw a
  refine ⟨?_,?_,subdivide_nodup 16 _ hn hc,subdivide_chain 16 (by decide) _ hc,?_⟩
  · simp only [route,point,subdivide_head 16 (by decide),hh,Option.map_some]
  · simp only [route,point,subdivide_getLast,ht,Option.map_some]
  · have hb := subdivide_length_le 16 (by decide) (SatCompleteDrawing.route x a)
    change (route x a).length≤_ at hb
    omega

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (v : Vertex x) :
    point x v∈route x a ↔ v=SatCompleteDrawing.source x a ∨ v=SatCompleteDrawing.target x a := by
  rw [point,route,scale_mem_subdivide_iff 16 (by decide) _
    (SatCompleteDrawing.route_certificate x hw a).2.2.2.1]
  exact SatCompleteDrawing.actual_vertex_clear x hw a v

theorem unrelated_vertex_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (v : Vertex x)
    (hs : v ≠SatCompleteDrawing.source x a) (ht : v ≠SatCompleteDrawing.target x a)
    (q : Point) (hq : q ∈route x a) :
    16≤IntegerGrid.manhattan q (point x v) := by
  apply subdivide_vertex_clearance 16 _ (SatCompleteDrawing.route_certificate x hw a).2.2.2.1
    (SatCompleteDrawing.point x v) _ q hq
  intro h
  exact ((SatCompleteDrawing.actual_vertex_clear x hw a v).mp h).elim hs ht

theorem unrelated_gadget_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (v : Vertex x)
    (hs : v ≠SatCompleteDrawing.source x a) (ht : v ≠SatCompleteDrawing.target x a)
    (i : Fin 4) (q : Point) (hq : q ∈route x a) :
    13≤IntegerGrid.manhattan q (SatBipartitePlacement.point x hw (v,i)) := by
  have hd := unrelated_vertex_distance x hw a v hs ht q hq
  have hg := DirectedScaledLayout.distance_to_anchor (SatCompleteDrawing.point x v)
    (SatBipartitePorts.choose x hw v).direction (SatBipartitePorts.choose x hw v).incoming i
  change IntegerGrid.manhattan (point x v) (SatBipartitePlacement.point x hw (v,i))≤3 at hg
  have htri := IntegerGrid.manhattan_triangle q (SatBipartitePlacement.point x hw (v,i)) (point x v)
  rw [IntegerGrid.manhattan_comm (SatBipartitePlacement.point x hw (v,i)) (point x v)] at htri
  omega

end GridHardness.SatScaledDrawing
