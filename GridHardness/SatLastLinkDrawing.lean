/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalLastLinks
public import GridHardness.SatRetiredSideDrawing

/-!
# SAT Last Link Drawing

The final crossing in each nonempty occurrence row has two links to
the retired XOR's false side. These are actual final-graph arcs with
short, mutually disjoint lattice routes in the common vertex placement.
No assertion about the remaining intercell or residual arcs is made.
-/

@[expose] public section

namespace GridHardness.SatLastLinkDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
local instance (l m : List Point) : Decidable (l.Disjoint m) :=
  inferInstanceAs (Decidable (∀ q ∈ l, q ∉ m))

abbrev LastCell {N : Nat} (p : Equiv.Perm (Fin N)) :=
  {c : Fin N × Fin N // SatCrossingRetirement.Catalogue.lastRequest? p c.2 = some c.1}
abbrev Edge {N : Nat} (p : Equiv.Perm (Fin N)) := LastCell p × Bool

def localEdge (b : Bool) : Fin 66 := if b then 52 else 50

theorem localEdge_link (b : Bool) : SatCrossingRetirement.Links.LinkEdge (localEdge b) := by
  apply (SatCrossingRetirement.Links.linkEdge_iff_index _).mpr
  cases b <;> simp [localEdge]

def cell {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) : WireCrossingSchedule.Cell p :=
  ⟨e.1.val,(SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ e.1.property).1⟩

def sourceWire {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatCrossingWireVertices.Vertex p :=
  if e.2 then .inl (e.1.val.2,7) else .inr (cell e,LastLinks.rowPort false)

def targetWire {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatCrossingWireVertices.Vertex p :=
  if e.2 then .inr (cell e,LastLinks.rowPort true) else .inl (e.1.val.2,4)

def route {N : Nat} (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  SatCrossingLattice.route p e.1.val (localEdge e.2)

variable {N n m : Nat}

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := PermutationWirePlacement.vertex φ p (sourceWire e)

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := PermutationWirePlacement.vertex φ p (targetWire e)

theorem edge_is_arc (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) := by
  rcases e with ⟨c,b⟩
  cases b
  · exact LastLinks.placement_incoming φ p c.val.1 c.val.2 c.property
  · exact LastLinks.placement_outgoing φ p c.val.1 c.val.2 c.property

theorem source_point (p : Equiv.Perm (Fin N)) (e : Edge p) :
    SatCrossingWireVertices.point p (sourceWire e) =
      SatCrossingLattice.point p e.1.val (XorLine.Lattice.edge (localEdge e.2)).1 := by
  rcases e with ⟨c,b⟩
  cases b
  · rfl
  · change SatCrossingRetirement.Placement.point p
      (SatCrossingRetirement.Catalogue.lastRequest? p c.val.2) c.val.2 7 = _
    rw [c.property]
    exact SatCrossingRetirement.Placement.latest_false_unchanged p c.val.1 c.val.2
      (SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ c.property).1.1 3

theorem target_point (p : Equiv.Perm (Fin N)) (e : Edge p) :
    SatCrossingWireVertices.point p (targetWire e) =
      SatCrossingLattice.point p e.1.val (XorLine.Lattice.edge (localEdge e.2)).2 := by
  rcases e with ⟨c,b⟩
  cases b
  · change SatCrossingRetirement.Placement.point p
      (SatCrossingRetirement.Catalogue.lastRequest? p c.val.2) c.val.2 4 = _
    rw [c.property]
    exact SatCrossingRetirement.Placement.latest_false_unchanged p c.val.1 c.val.2
      (SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ c.property).1.1 0
  · rfl

theorem actualPoint_source (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e) =
      SatCrossingWireVertices.point (SatClauseOrder.permutation φ) (sourceWire e) :=
  SatGlobalVertexPlacement.actualPoint_wire φ _

theorem actualPoint_target (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e) =
      SatCrossingWireVertices.point (SatClauseOrder.permutation φ) (targetWire e) :=
  SatGlobalVertexPlacement.actualPoint_wire φ _

private theorem local_length : ∀ b : Bool, 3 ≤ (XorLine.Lattice.edgeRoute (localEdge b)).length := by
  decide +kernel

theorem route_certificate (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (SatCrossingWireVertices.point p (sourceWire e)) ∧
    (route p e).getLast? = some (SatCrossingWireVertices.point p (targetWire e)) ∧
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep ∧
    3 ≤ (route p e).length ∧ (route p e).length ≤ 17 := by
  rw [source_point,target_point]
  have h := SatCrossingLattice.route_certificate p e.1.val (localEdge e.2)
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_,h.2.2.2.2.2⟩
  simpa only [route,SatCrossingLattice.route,List.length_map] using local_length e.2

theorem actual_route_certificate (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    3 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 17 := by
  simpa only [actualPoint_source,actualPoint_target] using route_certificate (SatClauseOrder.permutation φ) e

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*N+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+522 :=
  SatCrossingLattice.coordinates_bounded p e.1.val q
    (SatCrossingLattice.route_in_box p e.1.val (localEdge e.2) q hq)

private theorem side_incident : ∀ v : Fin 8, ∃ i : Fin 6,
    v = (XorGadget.arc (SatCrossingRetirement.sideArc i)).1 ∨
    v = (XorGadget.arc (SatCrossingRetirement.sideArc i)).2 := by decide +kernel

/-- Any wire vertex lying on a last-cell link is one of its two geometric
endpoints, including the relocated original XOR vertices. -/
theorem wire_point_incident (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p)
    (hv : SatCrossingWireVertices.point p v ∈ route p e) :
    SatCrossingWireVertices.point p v = SatCrossingWireVertices.point p (sourceWire e) ∨
      SatCrossingWireVertices.point p v = SatCrossingWireVertices.point p (targetWire e) := by
  rw [source_point,target_point]
  cases v with
  | inl v =>
    obtain ⟨s,hs⟩ := side_incident v.2
    have hm := (SatCrossingRetirement.Sides.route_vertex_clear p v.1 s v.2).mpr hs
    by_cases hj : v.1 = e.1.val.2
    · rcases v with ⟨j,v⟩
      dsimp at hj
      subst j
      obtain ⟨w,hw,_,he⟩ := SatCrossingRetirement.Sides.own_link_intersection
        p e.1.val.1 e.1.val.2 e.1.property s (localEdge e.2) (localEdge_link e.2)
        _ hm hv
      have hlocal : SatCrossingWireVertices.point p (.inl (e.1.val.2,v)) =
          SatCrossingLattice.point p e.1.val (XorLine.x 0 w) := by
        rcases e with ⟨c,b⟩
        cases b
        · change XorLine.x 0 w = XorLine.row 0 false ∨ XorLine.x 0 w = XorLine.x 0 4 at he
          have hw4 : w = 4 := by simpa only [XorLine.x,XorLine.row,reduceCtorEq,
            false_or,Sum.inl.injEq,Prod.mk.injEq,true_and] using he
          subst w
          change SatCrossingRetirement.Sides.xorPoint p c.val.2 v = _
          rw [hw]
          change SatCrossingRetirement.Placement.point p
            (SatCrossingRetirement.Catalogue.lastRequest? p c.val.2) c.val.2 4 = _
          rw [c.property]
          exact SatCrossingRetirement.Placement.latest_false_unchanged p _ _
            (SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ c.property).1.1 0
        · change XorLine.x 0 w = XorLine.x 0 7 ∨ XorLine.x 0 w = XorLine.row 0 true at he
          have hw7 : w = 7 := by simpa only [XorLine.x,XorLine.row,reduceCtorEq,
            or_false,Sum.inl.injEq,Prod.mk.injEq,true_and] using he
          subst w
          change SatCrossingRetirement.Sides.xorPoint p c.val.2 v = _
          rw [hw]
          change SatCrossingRetirement.Placement.point p
            (SatCrossingRetirement.Catalogue.lastRequest? p c.val.2) c.val.2 7 = _
          rw [c.property]
          exact SatCrossingRetirement.Placement.latest_false_unchanged p _ _
            (SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ c.property).1.1 3
      exact he.imp
        (fun h => hlocal.trans (congrArg (SatCrossingLattice.point p e.1.val) h))
        (fun h => hlocal.trans (congrArg (SatCrossingLattice.point p e.1.val) h))
    · exact False.elim (List.disjoint_left.mp
        (SatCrossingRetirement.Sides.other_wire_links_disjoint p v.1 e.1.val.1 e.1.val.2
          hj s (localEdge e.2)) hm hv)
  | inr v =>
    by_cases hc : v.1.val = e.1.val
    · have hm : SatCrossingLattice.point p e.1.val v.2.val ∈
          SatCrossingLattice.route p e.1.val (localEdge e.2) := by
        simpa only [SatCrossingWireVertices.point,hc,route] using hv
      have hi := (SatCrossingLattice.route_vertex_clear p e.1.val (localEdge e.2) v.2.val).mp hm
      exact hi.imp
        (fun h => by change SatCrossingLattice.point p v.1.val v.2.val = _; rw [hc,h])
        (fun h => by change SatCrossingLattice.point p v.1.val v.2.val = _; rw [hc,h])
    · have hs := SatCrossingLattice.boxes_separated p v.1.val e.1.val hc _ _
        (SatCrossingLattice.point_in_box p v.1.val v.2.val)
        (SatCrossingLattice.route_in_box p e.1.val (localEdge e.2) _ hv)
      simp [SatCrossingWireVertices.point,IntegerGrid.manhattan] at hs

theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ route p e ↔ v = sourceWire e ∨ v = targetWire e := by
  constructor
  · exact fun h => (wire_point_incident p e v h).imp
      (fun h => SatCrossingWireVertices.point_injective p h)
      (fun h => SatCrossingWireVertices.point_injective p h)
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (route_certificate p e).1
    · exact List.mem_of_getLast? (route_certificate p e).2.1

theorem body_vertex_clear (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ))
    (v : PermutationWirePlacement.BodyVertex n m) :
    SatGlobalVertexPlacement.bodyPoint φ v ∉ route (SatClauseOrder.permutation φ) e := by
  intro h
  have hb := route_bounds (SatClauseOrder.permutation φ) e _ h
  rcases v with i | ⟨v,b⟩ | ⟨c,v⟩
  · fin_cases i <;> dsimp [SatGlobalVertexPlacement.bodyPoint,SatExteriorLattice.sentinel,
      SatVariableLattice.wireX] at hb <;> omega
  · have hx := SatVariablePlacement.point_x φ v b
    dsimp [SatGlobalVertexPlacement.bodyPoint,SatVariableLattice.wireX] at hb hx
    omega
  · have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
    change 0 ≤ (SatClauseOrder.point c v).1 ∧ _ at hb
    omega

theorem actual_vertex_clear (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ))
    (v : (SatClauseOrder.graph φ).Vertex) :
    SatGlobalVertexPlacement.actualPoint φ v ∈ route (SatClauseOrder.permutation φ) e ↔
      v = source φ (SatClauseOrder.permutation φ) e ∨
      v = target φ (SatClauseOrder.permutation φ) e := by
  obtain ⟨z,rfl⟩ := (SatGlobalVertexPlacement.equiv φ).surjective v
  rw [SatGlobalVertexPlacement.actualPoint_equiv]
  cases z with
  | inl b =>
    constructor
    · exact fun h => False.elim (body_vertex_clear φ e b h)
    · rintro (h | h)
      all_goals
        have he := congrArg (SatGlobalVertexPlacement.actualPoint φ) h
        rw [SatGlobalVertexPlacement.actualPoint_equiv] at he
      · exact he.symm ▸ List.mem_of_head? (actual_route_certificate φ e).1
      · exact he.symm ▸ List.mem_of_getLast? (actual_route_certificate φ e).2.1
  | inr w =>
    change SatCrossingWireVertices.point _ w ∈ _ ↔ _
    rw [wire_vertex_clear]
    have hs : SatGlobalVertexPlacement.equiv φ (.inr (sourceWire e)) =
        source φ (SatClauseOrder.permutation φ) e := rfl
    have ht : SatGlobalVertexPlacement.equiv φ (.inr (targetWire e)) =
        target φ (SatClauseOrder.permutation φ) e := rfl
    rw [← hs,← ht]
    simp only [Equiv.apply_eq_iff_eq,Sum.inr.injEq]

-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- The geometric proof unfolds the coordinates of the constructed routes.
set_option synthInstance.maxSize 2048 in
private theorem local_disjoint : ∀ b c : Bool, b ≠ c →
    (XorLine.Lattice.edgeRoute (localEdge b)).Disjoint
      (XorLine.Lattice.edgeRoute (localEdge c)) := by decide +kernel

/-- Distinct last-cell links have no common lattice point, even on the
same retired wire. -/
theorem routes_disjoint (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f) :
    (route p e).Disjoint (route p f) := by
  by_cases hc : e.1.val = f.1.val
  · have hc' : e.1 = f.1 := Subtype.ext hc
    have hb : e.2 ≠ f.2 := fun h => hne (Prod.ext hc' h)
    apply List.disjoint_left.mpr
    intro q he hf
    obtain ⟨u,hu,huq⟩ := List.mem_map.mp he
    obtain ⟨v,hv,hvq⟩ := List.mem_map.mp hf
    have huv : u = v :=
      (SatCrossingLattice.frame p e.1.val).injective (by simpa only [hc] using huq.trans hvq.symm)
    exact List.disjoint_left.mp (local_disjoint e.2 f.2 hb) hu (huv ▸ hv)
  · exact SatCrossingLattice.distinct_cell_routes_disjoint p e.1.val f.1.val hc
      (localEdge e.2) (localEdge f.2)

end GridHardness.SatLastLinkDrawing
