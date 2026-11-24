/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingResidualRoutes

/-!
# SAT Crossing Retirement Sides

The six endpoint-column edges of every retired XOR, placed simultaneously
using the actual last-request selection. These edges are separated from
crossing connectors and retained cell routes; they meet their own residual
lanes only at the intended XOR endpoints.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Sides
open CliffordSynthesis PermutationWireLayout SatCrossingLattice Segments
set_option autoImplicit false
variable {n : Nat} (p : Equiv.Perm (Fin n))

def route (i : Fin n) (e : Fin 6) : List Point :=
  Placement.edgeRoute p (Residual.rowEnd p i) i (.inr e)

def xorPoint (i : Fin n) (v : Fin 8) : Point :=
  Placement.point p (Residual.rowEnd p i) i v

private theorem row_before (i : Fin n) : Placement.LastBefore (Residual.rowEnd p i) i :=
  lastInRow_before p _ i (Residual.rowEnd_valid p i)

private theorem sidePoints_bounds : ∀ e : Fin 6, ∀ z∈sidePoints e, -4≤z ∧ z≤4 := by decide +kernel

/-- Side edges lie within four steps of either the variable height or the
clause height, on the corresponding endpoint column. -/
theorem route_segments (i : Fin n) (e : Fin 6) (q : Point) (hq : q ∈route p i e) :
    (q.1=512*((n:Int)+1)+65 ∧ 512*low i-4≤q.2 ∧ q.2≤512*low i+4) ∨
    (q.1=Placement.left (Residual.rowEnd p i) ∧ 512*high p i-4≤q.2 ∧ q.2≤512*high p i+4) := by
  have hp := Placement.parameters p (Residual.rowEnd p i) i (row_before p i)
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
  have hb := sidePoints_bounds e z hz
  rw [Placement.frame_map]
  dsimp [sidePoint]
  split
  · left
    dsimp [finish]
    exact ⟨by omega,by omega,by omega⟩
  · right
    dsimp
    exact ⟨by omega,by omega,by omega⟩

theorem route_endpoints (i : Fin n) (e : Fin 6) :
    (route p i e).head?=some (xorPoint p i (XorGadget.arc (sideArc e)).1) ∧
    (route p i e).getLast?=some (xorPoint p i (XorGadget.arc (sideArc e)).2) :=
  Placement.edgeRoute_endpoints p _ i (row_before p i) (.inr e)

theorem route_simple (i : Fin n) (e : Fin 6) :
    (route p i e).Nodup ∧ (route p i e).IsChain UnitStep :=
  Placement.edgeRoute_simple p _ i (.inr e)

theorem route_vertex_clear (i : Fin n) (e : Fin 6) (v : Fin 8) :
    xorPoint p i v∈route p i e ↔
      v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2 :=
  Placement.edgeRoute_vertex_clear p _ i (row_before p i) (.inr e) v

theorem route_length (i : Fin n) (e : Fin 6) :
    3≤(route p i e).length ∧ (route p i e).length≤5 := by
  have hc := (SatCrossingRetirement.sideRoute_simple
    (Placement.span (Residual.rowEnd p i) i) (Placement.height p i) (Placement.tail i) e).2.2
  simpa only [route,Placement.edgeRoute,List.length_map,edgeRoute] using hc

theorem route_bounds (i : Fin n) (e : Fin 6) (q : Point) (hq : q ∈route p i e) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 :=
  Placement.edgeRoute_coordinates_bounded p _ i (row_before p i) (.inr e) q hq

/-- No false endpoint column is a row lane of any crossing cell. -/
theorem left_ne_lane (last : Option (Fin n)) (a : Fin n) (r : Fin 4) :
    Placement.left last≠SatCrossingRouting.lane a r := by
  intro he
  have hr := r.isLt
  have ha := low_bounds a
  cases last with
  | none => dsimp [Placement.left,SatCrossingRouting.lane] at he; omega
  | some b => dsimp [Placement.left,SatCrossingRouting.lane] at he; omega

theorem right_ne_lane (a : Fin n) (r : Fin 4) :
    512*((n:Int)+1)+65≠SatCrossingRouting.lane a r := by
  have ha := low_bounds a
  dsimp [SatCrossingRouting.lane]
  omega

/-- Every side edge is disjoint from every vertical intercell connector. -/
theorem vertical_disjoint (i a b c : Fin n) (e : Fin 6) (r : Fin 4)
    (hv : SatCrossingRouting.Consecutive p a b c) :
    (route p i e).Disjoint (SatCrossingRouting.route p a b c r) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hs := route_segments p i e q hq
  have hv' := (SatCrossingRouting.route_mem p a b c hv.2.2.1 r q).mp ht
  rcases hs with hs | hs
  · exact right_ne_lane a r (hs.1.symm.trans hv'.1)
  · exact left_ne_lane (Residual.rowEnd p i) a r (hs.1.symm.trans hv'.1)

/-- The last-request maximum also keeps every endpoint-column edge strictly
beyond the horizontal connectors on its own clause row. -/
theorem horizontal_disjoint (i a b c : Fin n) (e : Fin 6)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p a b c) :
    (route p i e).Disjoint (SatCrossingHorizontal.upperRoute p a b c) ∧
    (route p i e).Disjoint (SatCrossingHorizontal.lowerRoute p a b c) := by
  have hcommon : ∀ q, q∈route p i e →
      (q∈SatCrossingHorizontal.upperRoute p a b c ∨
       q∈SatCrossingHorizontal.lowerRoute p a b c) → False := by
    intro q hq ht
    have hs := route_segments p i e q hq
    have hr := SatCrossingHorizontal.route_bounds p a b c hh.2.2.1 q ht
    rcases hs with hs | hs
    · have hb := low_bounds b
      omega
    · have hic : i=c := high_injective p (by omega)
      subst c
      have hb := Separation.active_left_bound p (Residual.rowEnd p i) i b
        (Residual.rowEnd_valid p i) hh.2.1
      omega
  exact ⟨List.disjoint_left.mpr (fun _ hq ht => hcommon _ hq (Or.inl ht)),
    List.disjoint_left.mpr (fun _ hq ht => hcommon _ hq (Or.inr ht))⟩

/-- Two side edges of different occurrence wires occupy disjoint height
bands, including when their false columns happen to coincide. -/
theorem different_wire_sides (i j : Fin n) (hij : i ≠j) (e f : Fin 6) :
    (route p i e).Disjoint (route p j f) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hs := route_segments p i e q hq
  have hr := route_segments p j f q ht
  have hlo : low i≠low j := fun h => hij (low_injective h)
  have hhi : high p i≠high p j := fun h => hij (high_injective p h)
  have hil := low_bounds i
  have hjl := low_bounds j
  have hih := high_bounds p i
  have hjh := high_bounds p j
  rcases hs with hs | hs <;> rcases hr with hr | hr <;> omega

/-- Distinct side edges on one wire can meet only at a shared original XOR
endpoint. Combined with `different_wire_sides`, this covers all side pairs. -/
theorem same_wire_intersection (i : Fin n) (e f : Fin 6) (hef : e ≠f)
    (q : Point) (hq : q ∈route p i e) (ht : q ∈route p i f) :
    ∃ v : Fin 8, q=xorPoint p i v ∧
      (v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2) ∧
      (v=(XorGadget.arc (sideArc f)).1 ∨ v=(XorGadget.arc (sideArc f)).2) :=
  Placement.edgeRoute_intersection p _ i (row_before p i) (.inr e) (.inr f)
    (fun h => hef (Sum.inr.inj h)) q hq ht

/-- Side edges on one wire avoid every complete mandatory lane on another
wire; therefore they also avoid all of that wire's residual pieces. -/
theorem other_wire_whole_disjoint (i j : Fin n) (hij : i ≠j) (e : Fin 6) (r : Fin 4) :
    (route p i e).Disjoint (Placement.route p (Residual.rowEnd p j) j r) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hs := route_segments p i e q hq
  have hm := (whole_mem p _ j (row_before p j) r q).mp ht
  have ho := offset_bounds r
  have hlo : low i≠low j := fun h => hij (low_injective h)
  have hhi : high p i≠high p j := fun h => hij (high_injective p h)
  have hil := low_bounds i
  have hjl := low_bounds j
  have hih := high_bounds p i
  have hjh := high_bounds p j
  rcases hs with hs | hs <;> rcases hm with hm | hm | hm
  · omega
  · exact right_ne_lane j r (hs.1.symm.trans hm.1)
  · omega
  · omega
  · exact left_ne_lane (Residual.rowEnd p i) j r (hs.1.symm.trans hm.1)
  · omega

theorem other_wire_residual_disjoint (i : Fin n) (e : Fin 6) (v : Residual.Index p)
    (hiv : i ≠v.1) : (route p i e).Disjoint (Residual.route p v) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  exact List.disjoint_left.mp (other_wire_whole_disjoint p i v.1 hiv e v.2.1) hq
    (Residual.path_subset p _ v.1 (row_before p v.1) v.2.1 v.2.2 ht)

/-- A side edge meeting a residual lane on its own wire shares one of the
original XOR endpoints. -/
theorem same_wire_residual_intersection (i : Fin n) (e : Fin 6) (r : Fin 4)
    (part : Residual.Portion p i) (q : Point) (hq : q ∈route p i e)
    (ht : q ∈Residual.path p (Residual.rowEnd p i) i r part) :
    ∃ v : Fin 8, q=xorPoint p i v ∧
      (v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2) ∧
      (v=(XorGadget.arc (XorLine.Marked.crossArc r)).1 ∨ v=(XorGadget.arc (XorLine.Marked.crossArc r)).2) :=
  Placement.edgeRoute_intersection p _ i (row_before p i) (.inr e) (.inl r)
    (by intro h; cases h) q hq
    (Residual.path_subset p _ i (row_before p i) r part ht)

/-- If a side-edge point lies in a crossing box, that box must be the last
horizontal crossing on this wire. -/
theorem box_location (i : Fin n) (e : Fin 6) (q : Point) (hq : q ∈route p i e)
    (d : Cell n) (hd : InBox p d q) :
    Residual.rowEnd p i=some d.1 ∧ d.2=i := by
  have hs := route_segments p i e q hq
  dsimp [InBox] at hd
  rcases hs with hs | hs
  · have hb := low_bounds d.1
    omega
  · have hi : d.2=i := high_injective p (by omega)
    refine ⟨?_,hi⟩
    cases he : Residual.rowEnd p i with
    | none =>
      rw [he] at hs
      dsimp [Placement.left] at hs
      have hb := low_bounds d.1
      omega
    | some a =>
      rw [he] at hs
      dsimp [Placement.left] at hs
      have ha : a=d.1 := low_injective (by omega)
      rw [ha]

/-- Every side edge avoids all retained cell-internal routes. -/
theorem retained_routes_disjoint (i : Fin n) (e : Fin 6) (d : Cell n) (f : Fin 66)
    (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge f).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge f).2) :
    (route p i e).Disjoint (SatCrossingLattice.route p d f) := by
  apply List.disjoint_left.mpr
  intro q hq hf
  obtain ⟨he,hi⟩ := box_location p i e q hq d (SatCrossingLattice.route_in_box p d f q hf)
  have hb := Segments.retained_route_bound p d f hs ht q hf
  have hm := route_segments p i e q hq
  rcases hm with hm | hm
  · have hd := low_bounds d.1
    omega
  · rw [he] at hm
    dsimp [Placement.left] at hm
    omega

private theorem local_link_height : ∀ e : Fin 66, (e=50 ∨ e=52) →
    ∀ q∈XorLine.Lattice.edgeRoute e, q.1≤6 ∨ 14≤q.1 := by decide +kernel

theorem link_height (a i : Fin n) (f : Fin 66) (hf : Links.LinkEdge f)
    (q : Point) (hq : q ∈SatCrossingLattice.route p (a, i) f) :
    q.2≤512*high p i-4 ∨ 512*high p i+4≤q.2 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
  have hb := local_link_height f ((Links.linkEdge_iff_index f).mp hf) t ht
  rw [SatCrossingLattice.frame_map]
  dsimp
  omega

/-- Links on a different wire's clause row cannot meet a side edge. -/
theorem other_wire_links_disjoint (i a j : Fin n) (hij : i ≠j) (e : Fin 6)
    (f : Fin 66) : (route p i e).Disjoint (SatCrossingLattice.route p (a,j) f) := by
  apply List.disjoint_left.mpr
  intro q hq hf
  have h := (box_location p i e q hq (a,j) (SatCrossingLattice.route_in_box p _ f q hf)).2
  exact hij h.symm

/-- The final row-zero links can meet a side edge only at a common false
endpoint, completing their interface with all ten retired-XOR edges. -/
theorem own_link_intersection (a i : Fin n) (ha : Residual.rowEnd p i =some a)
    (e : Fin 6) (f : Fin 66) (hf : Links.LinkEdge f)
    (q : Point) (hq : q ∈route p i e) (hlink : q ∈SatCrossingLattice.route p (a, i) f) :
    ∃ v : Fin 8, q=xorPoint p i v ∧
      (v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2) ∧
      (XorLine.x 0 v=(XorLine.Lattice.edge f).1 ∨ XorLine.x 0 v=(XorLine.Lattice.edge f).2) := by
  have hl := row_before p i
  have hai : a < i := hl a ha
  have hs := route_segments p i e q hq
  have hb := Links.link_bounds p a i f hf q hlink
  have hy := link_height p a i f hf q hlink
  have ha' := low_bounds a
  have hx : q.1=Placement.left (Residual.rowEnd p i) := by
    rcases hs with hs | hs
    · omega
    · exact hs.1
  have hp : ∃ r : Fin 4, q=xorPoint p i (falseVertex r) := by
    rcases hs with hs | hs
    · omega
    · rcases hy with hy | hy
      · refine ⟨3,?_⟩
        rw [xorPoint,Placement.false_coordinates p _ i hl 3]
        dsimp [offset]
        exact Prod.ext hx (by omega)
      · refine ⟨0,?_⟩
        rw [xorPoint,Placement.false_coordinates p _ i hl 0]
        dsimp [offset]
        exact Prod.ext hx (by omega)
  obtain ⟨r,hr⟩ := hp
  refine ⟨falseVertex r,hr,?_,?_⟩
  · exact (route_vertex_clear p i e (falseVertex r)).mp (hr ▸ hq)
  · have hq' : q=point p (a,i) (XorLine.x 0 (falseVertex r)) := by
      rw [hr,xorPoint,ha,Placement.latest_false_unchanged p a i hai r]
    rw [hq'] at hlink
    exact (SatCrossingLattice.route_vertex_clear p (a,i) f _).mp hlink

/-- An outer XOR vertex on a final residual route is an actual list endpoint
of that route, not an interior point of a remaining segment. -/
theorem residual_outer_endpoint (i : Fin n) (r : Fin 4) (part : Residual.Portion p i)
    (q : Point) (hq : q ∈Residual.path p (Residual.rowEnd p i) i r part)
    (hout : q =xorPoint p i (trueVertex r) ∨ q =xorPoint p i (falseVertex r)) :
    (Residual.path p (Residual.rowEnd p i) i r part).head?=some q ∨
    (Residual.path p (Residual.rowEnd p i) i r part).getLast?=some q := by
  have hl := row_before p i
  cases part with
  | unsplit he =>
    have hc := Placement.edgeRoute_endpoints p _ i hl (.inl r)
    change (Placement.route p (Residual.rowEnd p i) i r).head?=
      some (xorPoint p i (XorGadget.arc (XorLine.Marked.crossArc r)).1) ∧
      (Placement.route p (Residual.rowEnd p i) i r).getLast?=
      some (xorPoint p i (XorGadget.arc (XorLine.Marked.crossArc r)).2) at hc
    rw [(crossArc_endpoints r).1,(crossArc_endpoints r).2] at hc
    by_cases hr : r.val%2=0
    · simp only [hr,ite_true] at hc
      rcases hout with rfl | rfl
      · exact Or.inr hc.2
      · exact Or.inl hc.1
    · simp only [hr,ite_false] at hc
      rcases hout with rfl | rfl
      · exact Or.inl hc.1
      · exact Or.inr hc.2
  | above j hj =>
    have hu := (upper_mem p _ i j hl hj.1 r q).mp hq
    have hfalse : q=xorPoint p i (falseVertex r) := by
      rcases hout with ht | hf
      · rw [ht,xorPoint,Placement.true_coordinates p _ i hl r] at hu
        have hi := low_bounds i
        have hh := high_bounds p j
        have hh' := (high_lt_high p).mpr hj.1.2
        have ho := offset_bounds r
        dsimp at hu
        rcases hu with hu | hu <;> omega
      · exact hf
    have hc := upper_endpoints p _ i j hl hj.1 r
    by_cases hr : r.val%2=0
    · simp only [hr,ite_true] at hc
      exact Or.inl (hc.1.trans (congrArg some hfalse.symm))
    · simp only [hr,ite_false] at hc
      exact Or.inr (hc.2.trans (congrArg some hfalse.symm))
  | below j hj =>
    have hu := (lower_mem p _ i j hl hj.1 r q).mp hq
    have htrue : q=xorPoint p i (trueVertex r) := by
      rcases hout with ht | hf
      · exact ht
      · rw [hf,xorPoint,Placement.false_coordinates p _ i hl r] at hu
        have hi := low_bounds i
        have hh := high_bounds p j
        have hh' := (high_lt_high p).mpr hj.1.2
        have ho := offset_bounds r
        dsimp at hu
        rcases hu with hu | hu <;> omega
    have hc := lower_endpoints p _ i j hl hj.1 r
    by_cases hr : r.val%2=0
    · simp only [hr,ite_true] at hc
      exact Or.inr (hc.2.trans (congrArg some htrue.symm))
    · simp only [hr,ite_false] at hc
      exact Or.inl (hc.1.trans (congrArg some htrue.symm))

/-- Every side-edge/residual intersection on a wire is a literal endpoint
of both explicit lists. -/
theorem same_wire_residual_endpoints (i : Fin n) (e : Fin 6) (r : Fin 4)
    (part : Residual.Portion p i) (q : Point) (hq : q ∈route p i e)
    (ht : q ∈Residual.path p (Residual.rowEnd p i) i r part) :
    ((route p i e).head?=some q ∨ (route p i e).getLast?=some q) ∧
    ((Residual.path p (Residual.rowEnd p i) i r part).head?=some q ∨
      (Residual.path p (Residual.rowEnd p i) i r part).getLast?=some q) := by
  obtain ⟨v,hv,hve,hvr⟩ := same_wire_residual_intersection p i e r part q hq ht
  constructor
  · have hc := route_endpoints p i e
    rcases hve with he | he
    · exact Or.inl (hc.1.trans (congrArg some (hv.trans (congrArg (xorPoint p i) he)).symm))
    · exact Or.inr (hc.2.trans (congrArg some (hv.trans (congrArg (xorPoint p i) he)).symm))
  · apply residual_outer_endpoint p i r part q ht
    rw [(crossArc_endpoints r).1,(crossArc_endpoints r).2] at hvr
    have he : v=trueVertex r ∨ v=falseVertex r := by
      split_ifs at hvr <;> tauto
    rcases he with he | he
    · exact Or.inl (hv.trans (congrArg (xorPoint p i) he))
    · exact Or.inr (hv.trans (congrArg (xorPoint p i) he))

end GridHardness.SatCrossingRetirement.Sides
