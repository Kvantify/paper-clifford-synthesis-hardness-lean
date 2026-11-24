/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteRoutes
public import GridHardness.LatticeEndpointNeighborhood

/-!
# SAT Bipartite Route Clearance

Every vertex of the bipartite replacement is clear of an external
route except for its two designated ports. Quantitative separation handles
unrelated gadgets; near either original endpoint, subdivision and trimming
locate the route on its intended cardinal ray.
-/

public section

namespace GridHardness.SatBipartiteRouteClearance
open CliffordComplexity CliffordSynthesis DirectedLocalLayout LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem trim_index_bounds {α : Type*} (a b : Nat) (l : List α)
    (hn : l.Nodup) (q : α) (hq : q ∈LatticeRouteTrim.trim a b l)
    (i : Nat) (hi : i <l.length) (he : q =l[i]) :
    a ≤ i ∧ i < l.length - b := by
  obtain ⟨j,hj,hjq⟩ := List.mem_iff_getElem.mp hq
  rw [LatticeRouteTrim.getElem] at hjq
  have hei : a+j=i := hn.getElem_inj_iff.mp (hjq.trans he)
  rw [LatticeRouteTrim.length] at hj
  omega

private theorem interpolate_at_endpoint (x : SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) (a : SatCompleteDrawing.Arc x) (b : Bool) (k : Nat) :
    interpolate 16
      (LatticeRouteDirections.endpointPoint (SatCompleteDrawing.route x a) b
        (by have := SatCompleteDrawing.route_length_lower x a; omega))
      (LatticeRouteDirections.neighborPoint (SatCompleteDrawing.route x a) b
        (by have := SatCompleteDrawing.route_length_lower x a; omega)) k=
      ((DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).1+
        (ray (SatCompleteDrawing.direction x a b) k).1,
       (DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).2+
        (ray (SatCompleteDrawing.direction x a b) k).2) := by
  rw [SatBipartiteRoutes.endpointPoint_eq x hw,SatCompleteDrawing.direction_spec x hw]
  generalize SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b)=p
  generalize SatCompleteDrawing.direction x a b=d
  fin_cases d <;> simp [interpolate,LatticeRouteDirections.step,ray,DirectedScaledLayout.anchor]

/-- A point of an external route close to its original endpoint lies
on the correct ray beyond the portion removed by trimming. -/
theorem endpoint_neighborhood (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : SatCompleteDrawing.Arc x) (b : Bool) (q : Point)
    (hq : q ∈SatBipartiteRoutes.route x hw a)
    (hd : IntegerGrid.manhattan
      (scale 16 (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))) q <16) :
    ∃ k, k<16 ∧ SatBipartiteRoutes.radius x hw a b≤k ∧
      q=((DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).1+
        (ray (SatCompleteDrawing.direction x a b) k).1,
       (DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).2+
        (ray (SatCompleteDrawing.direction x a b) k).2) := by
  have hc := SatCompleteDrawing.route_certificate x hw a
  have hl : 2≤(SatCompleteDrawing.route x a).length := by
    have := SatCompleteDrawing.route_length_lower x a
    omega
  have hlen := SatScaledDrawing.route_length_lower x a
  have hn := (SatScaledDrawing.route_certificate x hw a).2.2.1
  have hqs := SatBipartiteRoutes.mem_scaled x hw a q hq
  rw [← SatBipartiteRoutes.endpointPoint_eq x hw] at hd
  cases b
  · have hd' : IntegerGrid.manhattan
        (scale 16 ((SatCompleteDrawing.route x a)[0]'(by omega))) q<16 := hd
    obtain ⟨k,hk,hqi⟩ := getElem_initial_neighborhood 16 (by decide)
      (SatCompleteDrawing.route x a) hc.2.2.1 hc.2.2.2.1 hl q hqs hd'
    have hb := trim_index_bounds (SatBipartiteRoutes.radius x hw a false)
      (SatBipartiteRoutes.radius x hw a true) (SatScaledDrawing.route x a)
      hn q hq k (by omega) hqi
    refine ⟨k,hk,hb.1,?_⟩
    have he := hqi.trans (subdivide_getElem_initial 16 (SatCompleteDrawing.route x a) hl k hk)
    exact he.trans (interpolate_at_endpoint x hw a false k)
  · have hd' : IntegerGrid.manhattan
        (scale 16 ((SatCompleteDrawing.route x a)[(SatCompleteDrawing.route x a).length-1]'
          (by omega))) q<16 := by
      simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient] using hd
    obtain ⟨k,hk,hqi⟩ := getElem_terminal_neighborhood 16 (by decide)
      (SatCompleteDrawing.route x a) hc.2.2.1 hc.2.2.2.1 hl q hqs hd'
    have hb := trim_index_bounds (SatBipartiteRoutes.radius x hw a false)
      (SatBipartiteRoutes.radius x hw a true) (SatScaledDrawing.route x a)
      hn q hq ((SatScaledDrawing.route x a).length-1-k) (by omega) hqi
    refine ⟨k,hk,by omega,?_⟩
    have he := hqi.trans (subdivide_getElem_terminal 16 (by decide)
      (SatCompleteDrawing.route x a) hl k hk)
    have he' : q=interpolate 16
        (LatticeRouteDirections.endpointPoint (SatCompleteDrawing.route x a) true hl)
        (LatticeRouteDirections.neighborPoint (SatCompleteDrawing.route x a) true hl) k := by
      simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.neighborPoint,
        LatticeRouteDirections.orient,Nat.sub_sub] using he
    exact he'.trans (interpolate_at_endpoint x hw a true k)

private theorem local_port_unique (d e : Fin 4) (incoming b : Bool) (i : Fin 4) (k : Nat)
    (hd : e =d ↔ b =incoming) (hk : (if b =incoming then 3 else 0) ≤k)
    (he : vertexPoint d incoming i =ray e k) : i=SatBipartitePlacement.portIndex b := by
  by_cases hb : b=incoming
  · have hed := hd.mpr hb
    subst e
    subst b
    cases incoming <;> fin_cases i <;> fin_cases d <;>
      simp_all [vertexPoint,ray,SatBipartitePlacement.portIndex] <;> omega
  · have hed : d≠e := fun h => hb (hd.mp h.symm)
    have hk0 : k=0 := by
      by_contra hkn
      exact other_port_disjoint d e hed incoming i (by omega) he
    apply vertexPoint_injective d incoming
    rw [he,hk0,ray_zero]
    cases incoming <;> cases b <;> simp_all [vertexPoint,SatBipartitePlacement.portIndex]

/-- Within either endpoint gadget, the only vertex on the external route
is the incoming or outgoing port selected by that endpoint. -/
theorem endpoint_gadget_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : SatCompleteDrawing.Arc x) (b : Bool) (i : Fin 4)
    (hq : SatBipartitePlacement.point x hw (SatCompleteDrawing.endpointVertex x a b, i)
      ∈ SatBipartiteRoutes.route x hw a) : i=SatBipartitePlacement.portIndex b := by
  let v := SatCompleteDrawing.endpointVertex x a b
  let c := SatBipartitePorts.choose x hw v
  have hdist := DirectedScaledLayout.distance_to_anchor (SatCompleteDrawing.point x v)
    c.direction c.incoming i
  have hd : IntegerGrid.manhattan (scale 16 (SatCompleteDrawing.point x v))
      (SatBipartitePlacement.point x hw (v,i))<16 := lt_of_le_of_lt hdist (by decide)
  obtain ⟨k,_,hk,he⟩ := endpoint_neighborhood x hw a b _ hq hd
  have he' : vertexPoint c.direction c.incoming i=ray (SatCompleteDrawing.direction x a b) k := by
    change ((DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).1+
        (vertexPoint c.direction c.incoming i).1,
      (DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).2+
        (vertexPoint c.direction c.incoming i).2)=
      ((DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).1+
        (ray (SatCompleteDrawing.direction x a b) k).1,
       (DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).2+
        (ray (SatCompleteDrawing.direction x a b) k).2) at he
    exact Prod.ext (Int.add_left_cancel (congrArg Prod.fst he))
      (Int.add_left_cancel (congrArg Prod.snd he))
  have hi := c.direction_iff (⟨(a,b),rfl⟩ : SatCompleteDrawing.Incidence x v)
  exact local_port_unique c.direction (SatCompleteDrawing.direction x a b)
    c.incoming b i k hi hk he'

/-- Every actual bipartite vertex lies on an external route exactly when
it is one of the two designated endpoint ports. -/
theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : SatCompleteDrawing.Arc x) (z : SatBipartitePlacement.Vertex x) :
    SatBipartitePlacement.point x hw z∈SatBipartiteRoutes.route x hw a ↔
      z=(SatCompleteDrawing.source x a,3) ∨ z=(SatCompleteDrawing.target x a,0) := by
  rcases z with ⟨v,i⟩
  constructor
  · intro hq
    by_cases hs : v=SatCompleteDrawing.source x a
    · subst v
      have hi := endpoint_gadget_clear x hw a false i hq
      exact Or.inl (Prod.ext rfl hi)
    · by_cases ht : v=SatCompleteDrawing.target x a
      · subst v
        have hi := endpoint_gadget_clear x hw a true i hq
        exact Or.inr (Prod.ext rfl hi)
      · have hd := SatBipartiteRoutes.unrelated_gadget_distance x hw a v hs ht i _ hq
        simp [IntegerGrid.manhattan] at hd
  · rintro (h | h)
    · rw [h]
      exact List.mem_of_head? (SatBipartiteRoutes.route_certificate x hw a).1
    · rw [h]
      exact List.mem_of_getLast? (SatBipartiteRoutes.route_certificate x hw a).2.1

end GridHardness.SatBipartiteRouteClearance
