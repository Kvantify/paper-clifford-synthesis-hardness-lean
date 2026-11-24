/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBodyChainDrawing
public import GridHardness.SatClauseWireEdges

/-!
# SAT Outer Drawing

Simultaneous routes for the SAT bodies, occurrence chains, exterior
backbone, and clause links. Every indexed route represents an actual
final-graph arc and distinct routes meet only at common endpoints. Internal
wire arcs are not included, so this is not a complete graph drawing.
-/

@[expose] public section

namespace GridHardness.SatOuterDrawing
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Edge (x : SatTy.denote) :=
  SatBodyChainDrawing.Edge x ⊕ (Occurrence x.length × Bool)

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatBodyChainDrawing.source x e
  | .inr (o,b) => SatClauseWireDrawing.source (finiteFormula x) o b

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatBodyChainDrawing.target x e
  | .inr (o,b) => SatClauseWireDrawing.target (finiteFormula x) o b

def route (x : SatTy.denote) : Edge x → List Point
  | .inl e => SatBodyChainDrawing.route x e
  | .inr (o,b) => SatClauseWireDrawing.route (finiteFormula x) o b

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  rcases e with e | ⟨o,b⟩
  · exact SatBodyChainDrawing.edge_is_arc x e
  · exact SatClauseWireDrawing.edge_is_arc (finiteFormula x) o b

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 4096*(x.length+1) := by
  rcases e with e | ⟨o,b⟩
  · exact SatBodyChainDrawing.route_certificate x hw e
  · have he := SatClauseWireDrawing.route_endpoints (finiteFormula x) o b
    have hs := SatClauseWireDrawing.route_simple (finiteFormula x) o b
    have hl := SatClauseWireDrawing.route_length (finiteFormula x) o b
    exact ⟨he.1,he.2,hs.1,hs.2,by change 2 ≤ (SatClauseWireDrawing.route _ o b).length; omega,
      by change (SatClauseWireDrawing.route _ o b).length ≤ _; omega⟩

/-- Every outer route has at least eight steps, including the shortest
internal clause edges. This bound does not need a formula-width premise. -/
theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    9 ≤ (route x e).length := by
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      cases e with
      | direct v =>
        by_cases hc : SatVariableOrder.count (finiteFormula x) v = 0
        · have h := SatVariableLattice.emptyRoute_certificate (3*x.length)
            (SatVariableOrder.prefix (finiteFormula x) v)
          simp only [route,SatBodyChainDrawing.route,SatBodyDrawing.route,
            SatVariableDrawing.route,ite_eq_left hc]
          omega
        · have hp : SatVariableOrder.prefix (finiteFormula x) v <
              SatVariableOrder.prefix (finiteFormula x) v+
                SatVariableOrder.count (finiteFormula x) v := by omega
          have h := SatVariableLattice.directRoute_certificate (3*x.length) _ _ hp
          simp only [route,SatBodyChainDrawing.route,SatBodyDrawing.route,
            SatVariableDrawing.route,ite_eq_right hc]
          omega
      | backbone v w h =>
        simp only [route,SatBodyChainDrawing.route,SatBodyDrawing.route,
          SatVariableDrawing.route,SatVariableLattice.backboneRoute,SatCrossingRouting.rising_length]
        omega
    | inr e =>
      cases e with
      | internal c e =>
        have hmin : ∀ f : Fin 14, 8 ≤ PlanarSatClause.Lattice.length f := by decide +kernel
        simp only [route,SatBodyChainDrawing.route,SatBodyDrawing.route,SatClauseDrawing.route,
          SatClauseOrder.route,SatClausePlacement.route,List.length_map,
          PlanarSatClause.Lattice.route_length]
        exact Nat.succ_le_succ (hmin e)
      | backbone c d h =>
        simp only [route,SatBodyChainDrawing.route,SatBodyDrawing.route,SatClauseDrawing.route,
          SatClauseBackbone.route_length]
        omega
  · cases e with
    | entry v h =>
      simp only [route,SatBodyChainDrawing.route,SatVariableChainDrawing.route,
        SatVariableLattice.entryRoute_length]
      omega
    | between v k l h =>
      simp only [route,SatBodyChainDrawing.route,SatVariableChainDrawing.route,
        SatVariableLattice.betweenRoute,SatCrossingRouting.rising_length]
      omega
    | exit v h =>
      simp only [route,SatBodyChainDrawing.route,SatVariableChainDrawing.route,
        SatVariableLattice.exitRoute_length]
      omega
  · cases e <;>
      simp [route,SatBodyChainDrawing.route,SatExteriorDrawing.route,
        SatExteriorLattice.down,SatExteriorLattice.bottom,SatExteriorLattice.firstVariable,
        SatCrossingRouting.rising_length,SatExteriorLattice.forward_length,
        SatExteriorLattice.returning_length,SatExteriorLattice.closing_length]
  · have h := SatClauseWireDrawing.route_length (finiteFormula x) o b
    change 9 ≤ (SatClauseWireDrawing.route (finiteFormula x) o b).length
    omega

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  rcases e with e | ⟨o,b⟩
  · exact SatBodyChainDrawing.actual_vertex_clear x hw e v
  · exact SatClauseWireDrawing.route_vertex_clear (finiteFormula x) o b v

theorem endpoints_ne (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) : source x e ≠ target x e := by
  obtain ⟨hh,ht,hn,_,hl,_⟩ := route_certificate x hw e
  intro he
  rw [he] at hh
  cases hr : route x e with
  | nil => simp [hr] at hl
  | cons a l =>
    have hne : l ≠ [] := by
      intro h
      simp [hr,h] at hl
    have ha : a = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e) := by
      simpa only [hr,List.head?_cons,Option.some.injEq] using hh
    have ht' : l.getLast? = some a := by
      simpa only [hr,List.getLast?_cons_of_ne_nil hne,ha] using ht
    exact (List.nodup_cons.mp (hr ▸ hn)).1 (List.mem_of_getLast? ht')

theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (q : Point) (hq : q ∈ route x e) :
    -128 ≤ q.1 ∧ q.1 ≤ SatVariableLattice.wireX (3*x.length)+128 ∧
      -64 ≤ q.2 ∧ q.2 ≤ SatExteriorLattice.top (3*x.length) := by
  rcases e with e | ⟨o,b⟩
  · exact SatBodyChainDrawing.route_bounds x hw e q hq
  · have h := SatClauseWireDrawing.route_bounds (finiteFormula x) o b q hq
    dsimp [SatVariableLattice.wireX,SatExteriorLattice.top]
    omega

/-- Any intersection of a clause link with the other outer routes is its
own clause endpoint. This also covers first and last clause backbone ports. -/
theorem clause_body_point (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (o : Occurrence x.length) (b : Bool) (e : SatBodyChainDrawing.Edge x) (q : Point)
    (hc : q ∈ SatClauseWireDrawing.route (finiteFormula x) o b)
    (he : q ∈ SatBodyChainDrawing.route x e) :
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x)
      (SatClauseWireDrawing.clauseVertex (finiteFormula x) o b) := by
  rw [SatClauseWireDrawing.clauseVertex,SatGlobalVertexPlacement.actualPoint_clause]
  change q = SatClauseOrder.point o.1
    (if b then clauseTop o.2 else clauseBottom o.2)
  rcases e with e | e | e
  · cases e with
    | inl e =>
      have h := SatClauseWireConnectorClearance.variable_body_separation (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) (SatWireLayout.variableRank (finiteFormula x) o)
        b e q q hc he
      simp [IntegerGrid.manhattan] at h
    | inr e =>
      have hb := SatClauseDrawing.route_bounds e q he
      have hl := (SatClauseWireLattice.route_mem _ _ b q).mp hc
      exact SatClauseWireConnectorClearance.clause_endpoint_of_x (finiteFormula x) o b q hc
        (by omega)
  · have h := SatClauseWireConnectorClearance.variable_chain_separation (finiteFormula x)
      (SatWireLayout.variableRank (finiteFormula x) o) b e q q hc he
    simp [IntegerGrid.manhattan] at h
  · cases e with
    | sentinelFirst =>
      have h := SatClauseWireConnectorClearance.down_separation
        (SatClauseOrder.permutation (finiteFormula x))
        (SatWireLayout.variableRank (finiteFormula x) o) b q q hc he
      simp [IntegerGrid.manhattan] at h
    | sentinelSecond =>
      have h := SatClauseWireConnectorClearance.bottom_separation
        (SatClauseOrder.permutation (finiteFormula x))
        (SatWireLayout.variableRank (finiteFormula x) o) b q q hc he
      simp [IntegerGrid.manhattan] at h
    | firstVariable =>
      have h := SatClauseWireConnectorClearance.first_variable_separation
        (SatClauseOrder.permutation (finiteFormula x))
        (SatWireLayout.variableRank (finiteFormula x) o) b q q hc he
      simp [IntegerGrid.manhattan] at h
    | forward hm =>
      have h := SatClauseWireConnectorClearance.forward_intersection (finiteFormula x) o b q hc he
      rw [h.2.2]
      exact h.2.1
    | returning hm =>
      have h := SatClauseWireConnectorClearance.returning_intersection (finiteFormula x) o b q hc he
      rw [h.2.2]
      exact h.2.1
    | closing hm =>
      have ho := o.1.isLt
      omega

theorem incident_of_vertex_mem (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (q : Point) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex)
    (hv : q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v)
    (he : q ∈ route x e) : Incident x e q := by
  rw [hv] at he
  exact ((actual_vertex_clear x hw e v).mp he).imp
    (fun h => hv.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))
    (fun h => hv.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))

theorem clause_body_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (o : Occurrence x.length) (b : Bool) (e : SatBodyChainDrawing.Edge x) (q : Point)
    (hc : q ∈ SatClauseWireDrawing.route (finiteFormula x) o b)
    (he : q ∈ SatBodyChainDrawing.route x e) :
    Incident x (.inr (o,b)) q ∧ Incident x (.inl e) q := by
  have hp := clause_body_point x hw o b e q hc he
  exact ⟨incident_of_vertex_mem x hw (.inr (o,b)) q _ hp hc,
    incident_of_vertex_mem x hw (.inl e) q _ hp he⟩

/-- Every pair of distinct indexed routes meets only at a shared endpoint.
No further compatibility premise between the assembled families is needed. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | ⟨o,a⟩
  · rcases f with f | ⟨t,b⟩
    · exact SatBodyChainDrawing.route_intersection x hw e f
        (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact (clause_body_intersection x hw t b e q hf he).symm
  · rcases f with f | ⟨t,b⟩
    · exact clause_body_intersection x hw o a f q he hf
    · exact False.elim (List.disjoint_left.mp
        (SatClauseWireDrawing.routes_disjoint (finiteFormula x) o t a b
          (fun h => hne (congrArg Sum.inr h))) he hf)

/-- A common route point is the placement of one actual graph vertex
incident to both edges, rather than merely two coincident coordinates. -/
theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∧
      (v = source x e ∨ v = target x e) ∧
      (v = source x f ∨ v = target x f) := by
  have h := (route_intersection x hw e f hne q he hf).1
  rcases h with h | h
  · exact ⟨source x e,h,Or.inl rfl,(actual_vertex_clear x hw f _).mp (h ▸ hf)⟩
  · exact ⟨target x e,h,Or.inr rfl,(actual_vertex_clear x hw f _).mp (h ▸ hf)⟩

end GridHardness.SatOuterDrawing
