/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatLastLinkDrawing

/-!
# SAT Residual Drawing

Directed endpoints of every final residual lane in the simultaneous
wire-vertex placement. The geometric certificate covers empty columns and
both extreme tails. `SatResidualArcs` proves graph adjacency for these endpoint pairs.
-/

@[expose] public section

namespace GridHardness.SatResidualDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
open SatCrossingRetirement SatCrossingRetirement.Segments
open XorLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Edge {N : Nat} (p : Equiv.Perm (Fin N)) := Residual.Index p

def input (r : Fin 4) : SatCrossingHorizontal.RetainedVertex :=
  ⟨XorLine.inputPort 4 (.inr r),by trivial⟩

def output (r : Fin 4) : SatCrossingHorizontal.RetainedVertex :=
  ⟨XorLine.outputPort 4 (.inr r),by trivial⟩

def sourceWire {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatCrossingWireVertices.Vertex p :=
  match e.2.2 with
  | .unsplit _ => .inl (e.1,(XorGadget.arc (Marked.crossArc e.2.1)).1)
  | .above j hj => if e.2.1.val%2=0 then .inl (e.1,falseVertex e.2.1)
      else .inr (⟨(e.1,j),hj.1⟩,output e.2.1)
  | .below j hj => if e.2.1.val%2=0 then .inr (⟨(e.1,j),hj.1⟩,output e.2.1)
      else .inl (e.1,trueVertex e.2.1)

def targetWire {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatCrossingWireVertices.Vertex p :=
  match e.2.2 with
  | .unsplit _ => .inl (e.1,(XorGadget.arc (Marked.crossArc e.2.1)).2)
  | .above j hj => if e.2.1.val%2=0 then .inr (⟨(e.1,j),hj.1⟩,input e.2.1)
      else .inl (e.1,falseVertex e.2.1)
  | .below j hj => if e.2.1.val%2=0 then .inl (e.1,trueVertex e.2.1)
      else .inr (⟨(e.1,j),hj.1⟩,input e.2.1)

def route {N : Nat} (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  Residual.route p e

variable {N n m : Nat}

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := PermutationWirePlacement.vertex φ p (sourceWire e)

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := PermutationWirePlacement.vertex φ p (targetWire e)

theorem route_endpoints (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (SatCrossingWireVertices.point p (sourceWire e)) ∧
    (route p e).getLast? = some (SatCrossingWireVertices.point p (targetWire e)) := by
  rcases e with ⟨i,r,part⟩
  have hl := Catalogue.last_before p i
  cases part with
  | unsplit he =>
    exact Placement.edgeRoute_endpoints p _ i hl (.inl r)
  | above j hj =>
    have h := upper_endpoints p (Residual.rowEnd p i) i j hl hj.1 r
    by_cases hr : r.val%2=0 <;>
      simpa only [route,Residual.route,Residual.path,sourceWire,targetWire,hr,
        ite_true,ite_false,SatCrossingWireVertices.point,SatCrossingWireVertices.retired,
        input,output,Residual.rowEnd] using h
  | below j hj =>
    have h := lower_endpoints p (Residual.rowEnd p i) i j hl hj.1 r
    by_cases hr : r.val%2=0 <;>
      simpa only [route,Residual.route,Residual.path,sourceWire,targetWire,hr,
        ite_true,ite_false,SatCrossingWireVertices.point,SatCrossingWireVertices.retired,
        input,output,Residual.rowEnd] using h

theorem actualPoint_source (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e) =
      SatCrossingWireVertices.point (SatClauseOrder.permutation φ) (sourceWire e) :=
  SatGlobalVertexPlacement.actualPoint_wire φ _

theorem actualPoint_target (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e) =
      SatCrossingWireVertices.point (SatClauseOrder.permutation φ) (targetWire e) :=
  SatGlobalVertexPlacement.actualPoint_wire φ _

theorem route_simple (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep :=
  Residual.route_simple p e

theorem route_length_bound (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).length ≤ 2048*(N+1) := Residual.route_length_bound p e

private theorem span_lower (last : Option (Fin N)) (i : Fin N)
    (hl : Placement.LastBefore last i) : 48 ≤ Placement.span last i := by
  have hi := PermutationWireLayout.low_bounds i
  cases last with
  | none => dsimp [Placement.span,Placement.left]; omega
  | some j =>
    have hj := PermutationWireLayout.low_lt_low (hl j rfl)
    dsimp [Placement.span,Placement.left]
    omega

theorem route_length_lower (p : Equiv.Perm (Fin N)) (e : Edge p) :
    3 ≤ (route p e).length := by
  rcases e with ⟨i,r,part⟩
  have hl := Catalogue.last_before p i
  have hp := Placement.parameters p (Residual.rowEnd p i) i hl
  have hs := span_lower (Residual.rowEnd p i) i hl
  have hr := r.isLt
  cases part with
  | unsplit he =>
    simp only [route,Residual.route,Residual.path,Placement.route,List.length_map,
      SatCrossingRetirement.route_length]
    omega
  | above j hj =>
    have hc := cut_bounds (Placement.span (Residual.rowEnd p i) i)
      (Placement.height p i) r (cutHeight p i j true)
      (cutHeight_bounds p i j hj.1 r true)
    dsimp [turn] at hc
    simp only [route,Residual.route,Residual.path,upper]
    split_ifs <;> simp only [List.length_reverse,List.length_map,headPath,List.length_range] <;> omega
  | below j hj =>
    have hc := cut_bounds (Placement.span (Residual.rowEnd p i) i)
      (Placement.height p i) r (cutHeight p i j false)
      (cutHeight_bounds p i j hj.1 r false)
    have hi := PermutationWireLayout.low_bounds i
    have ht : 1 ≤ Placement.tail i := by
      dsimp [Placement.tail]
      omega
    dsimp [turn] at hc
    simp only [route,Residual.route,Residual.path,lower]
    split_ifs <;> simp only [List.length_reverse,List.length_map,tailPath,List.length_range] <;>
      dsimp [finish] <;> omega

theorem actual_route_certificate (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    3 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 2048*(3*m+1) := by
  rw [actualPoint_source,actualPoint_target]
  exact ⟨(route_endpoints _ e).1,(route_endpoints _ e).2,(route_simple _ e).1,
    (route_simple _ e).2,route_length_lower _ e,route_length_bound _ e⟩

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*(N+1)+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+516 :=
  Residual.route_bounds p e q hq

theorem route_disjoint (p : Equiv.Perm (Fin N)) (e f : Edge p) (hef : e ≠ f) :
    (route p e).Disjoint (route p f) := Residual.route_disjoint p e f hef

private theorem side_incident : ∀ v : Fin 8, ∃ i : Fin 6,
    v = (XorGadget.arc (sideArc i)).1 ∨ v = (XorGadget.arc (sideArc i)).2 := by
  decide +kernel

/-- Residual lanes contain no other wire vertices, including vertices of
retired XORs on other wires and the remnants of every active crossing. -/
theorem wire_point_incident (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p)
    (hv : SatCrossingWireVertices.point p v ∈ route p e) :
    SatCrossingWireVertices.point p v = SatCrossingWireVertices.point p (sourceWire e) ∨
      SatCrossingWireVertices.point p v = SatCrossingWireVertices.point p (targetWire e) := by
  cases v with
  | inl v =>
    obtain ⟨s,hs⟩ := side_incident v.2
    have hm := (Sides.route_vertex_clear p v.1 s v.2).mpr hs
    by_cases hj : v.1 = e.1
    · rcases v with ⟨j,v⟩
      dsimp at hj
      subst j
      have h := (Sides.same_wire_residual_endpoints p e.1 s e.2.1 e.2.2 _ hm hv).2
      have he := route_endpoints p e
      rcases h with h | h
      · exact Or.inl (Option.some.inj (h.symm.trans he.1))
      · exact Or.inr (Option.some.inj (h.symm.trans he.2))
    · exact False.elim (List.disjoint_left.mp
        (Sides.other_wire_residual_disjoint p v.1 s e hj) hm hv)
  | inr v =>
    rcases e with ⟨i,r,part⟩
    have hl := Residual.rowEnd_valid p i
    cases part with
    | unsplit he =>
      exact False.elim (whole_retained_vertex_clear p _ i hl he r
        v.1.val v.1.property v.2 hv)
    | above j hj =>
      obtain ⟨hc,hv'⟩ := (upper_retained_vertex_clear p _ i j hl hj r
        v.1.val v.1.property v.2).mp hv
      change SatCrossingLattice.point p v.1.val v.2.val = _ ∨
        SatCrossingLattice.point p v.1.val v.2.val = _
      rw [hc,hv']
      by_cases hr : r.val%2=0 <;>
        simp [sourceWire,targetWire,SatCrossingRouting.lowerPort,hr,
          SatCrossingWireVertices.point,input,output]
    | below j hj =>
      obtain ⟨hc,hv'⟩ := (lower_vertex_clear p _ i j (Catalogue.last_before p i) hj r
        v.1.val v.1.property v.2.val).mp hv
      change SatCrossingLattice.point p v.1.val v.2.val = _ ∨
        SatCrossingLattice.point p v.1.val v.2.val = _
      rw [hc,hv']
      by_cases hr : r.val%2=0 <;>
        simp [sourceWire,targetWire,SatCrossingRouting.upperPort,hr,
          SatCrossingWireVertices.point,input,output]

theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ route p e ↔ v = sourceWire e ∨ v = targetWire e := by
  constructor
  · exact fun h => (wire_point_incident p e v h).imp
      (fun h => SatCrossingWireVertices.point_injective p h)
      (fun h => SatCrossingWireVertices.point_injective p h)
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (route_endpoints p e).1
    · exact List.mem_of_getLast? (route_endpoints p e).2

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
      · rw [actualPoint_source] at he
        change SatGlobalVertexPlacement.bodyPoint φ b = _ at he
        change SatGlobalVertexPlacement.bodyPoint φ b ∈ _
        rw [he]
        exact List.mem_of_head? (route_endpoints _ e).1
      · rw [actualPoint_target] at he
        change SatGlobalVertexPlacement.bodyPoint φ b = _ at he
        change SatGlobalVertexPlacement.bodyPoint φ b ∈ _
        rw [he]
        exact List.mem_of_getLast? (route_endpoints _ e).2
  | inr w =>
    change SatCrossingWireVertices.point _ w ∈ _ ↔ _
    rw [wire_vertex_clear]
    have hs : SatGlobalVertexPlacement.equiv φ (.inr (sourceWire e)) =
        source φ (SatClauseOrder.permutation φ) e := rfl
    have ht : SatGlobalVertexPlacement.equiv φ (.inr (targetWire e)) =
        target φ (SatClauseOrder.permutation φ) e := rfl
    rw [← hs,← ht]
    simp only [Equiv.apply_eq_iff_eq,Sum.inr.injEq]

end GridHardness.SatResidualDrawing
