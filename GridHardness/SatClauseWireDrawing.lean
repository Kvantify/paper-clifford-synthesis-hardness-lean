/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireConnectorClearance
public import GridHardness.SatClauseRetirementClearance

/-!
# SAT Clause Wire Drawing

Clause links as routes between explicitly named vertices of the final
SAT sweep graph. Their wire endpoint is the first retained crossing port,
or the original false XOR port when the request list is empty. Every other
final graph vertex is excluded from the route. Arc preservation is proved
separately from these endpoint and geometric certificates.
-/

@[expose] public section

namespace GridHardness.SatClauseWireDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
open SatClauseWireLattice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

variable {N n m : Nat}

def retainedPort (b : Bool) : SatCrossingHorizontal.RetainedVertex :=
  ⟨if b then XorLine.outputPort 4 (.inl false) else XorLine.inputPort 4 (.inl false),
    by cases b <;> decide⟩

def wireVertex (p : Equiv.Perm (Fin N)) (j : Fin N) (b : Bool) :
    SatCrossingWireVertices.Vertex p :=
  match hf : firstRequest? p j with
  | none => .inl (j, if b then 7 else 4)
  | some i => .inr (⟨(i,j),(firstRequest_sound p i j hf).1⟩,retainedPort b)

theorem wireVertex_none (p : Equiv.Perm (Fin N)) (j : Fin N) (b : Bool)
    (hf : firstRequest? p j = none) :
    wireVertex p j b = .inl (j, if b then 7 else 4) := by
  unfold wireVertex
  split
  · rfl
  · rename_i i hi
    rw [hf] at hi
    contradiction

theorem wireVertex_some (p : Equiv.Perm (Fin N)) (i j : Fin N) (b : Bool)
    (hf : firstRequest? p j = some i) :
    wireVertex p j b = .inr (⟨(i,j),(firstRequest_sound p i j hf).1⟩,retainedPort b) := by
  unfold wireVertex
  split
  · rename_i hn
    rw [hf] at hn
    contradiction
  · rename_i k hk
    have he : k = i := Option.some.inj (hk.symm.trans hf)
    subst k
    rfl

theorem wireVertex_point (p : Equiv.Perm (Fin N)) (j : Fin N) (b : Bool) :
    SatCrossingWireVertices.point p (wireVertex p j b) = wirePoint p j b := by
  cases hf : firstRequest? p j with
  | none =>
    rw [wireVertex_none p j b hf]
    exact (wire_endpoint_none p j hf b).symm
  | some i =>
    rw [wireVertex_some p i j b hf]
    exact (wire_endpoint_some p i j hf b).symm

private theorem side_incident : ∀ v : Fin 8, ∃ e : Fin 6,
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).1 ∨
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).2 := by decide +kernel

/-- The entire simultaneous wire-vertex placement meets a clause link
at exactly its chosen wire endpoint. -/
theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (j : Fin N) (b : Bool)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ SatClauseWireLattice.route p j b ↔
      v = wireVertex p j b := by
  constructor
  · intro h
    apply SatCrossingWireVertices.point_injective p
    rw [wireVertex_point]
    cases v with
    | inl iv =>
      rcases iv with ⟨i,v⟩
      obtain ⟨e,he⟩ := side_incident v
      have hs := (SatCrossingRetirement.Sides.route_vertex_clear p i e v).mpr he
      have hc := SatClauseRetirementClearance.side_intersection p j i b e _ h hs
      exact hc.2.2.1
    | inr cv =>
      rcases cv with ⟨c,v⟩
      exact (active_box_intersection p j b c.val c.property _
        h (SatCrossingLattice.point_in_box p c.val v.val)).2.2
  · rintro rfl
    rw [wireVertex_point]
    exact SatClauseRetirementClearance.wirePoint_mem p j b

def clausePort (o : Occurrence m) (b : Bool) : Fin 12 :=
  if b then clauseTop o.2 else clauseBottom o.2

noncomputable def clauseVertex (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).Vertex :=
  SatClauseOrder.vertex φ o.1 (clausePort o b)

noncomputable def actualWireVertex (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).Vertex :=
  PermutationWirePlacement.vertex φ (SatClauseOrder.permutation φ)
    (wireVertex (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b)

noncomputable def source (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).Vertex :=
  if b then actualWireVertex φ o b else clauseVertex φ o b

noncomputable def target (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).Vertex :=
  if b then clauseVertex φ o b else actualWireVertex φ o b

def route (φ : Formula n m) (o : Occurrence m) (b : Bool) : List Point :=
  SatClauseWireLattice.route (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b

theorem actualPoint_clauseVertex (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    SatGlobalVertexPlacement.actualPoint φ (clauseVertex φ o b) =
      clausePoint (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b := by
  rw [clauseVertex,SatGlobalVertexPlacement.actualPoint_clause]
  exact (clause_endpoint φ o b).symm

theorem actualPoint_actualWireVertex (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    SatGlobalVertexPlacement.actualPoint φ (actualWireVertex φ o b) =
      wirePoint (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b := by
  rw [actualWireVertex,SatGlobalVertexPlacement.actualPoint_wire,wireVertex_point]

theorem endpoints_ne (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    source φ o b ≠ target φ o b := by
  intro he
  have hp := congrArg (SatGlobalVertexPlacement.actualPoint φ) he
  have hb := finishX_bounds (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o)
  cases b <;> simp only [source,target,Bool.false_eq_true,ite_false,ite_true,
    actualPoint_clauseVertex,actualPoint_actualWireVertex] at hp
  all_goals
    have hx := congrArg Prod.fst hp
    dsimp [clausePoint,wirePoint] at hx
    omega

theorem route_endpoints (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (route φ o b).head? = some (SatGlobalVertexPlacement.actualPoint φ (source φ o b)) ∧
    (route φ o b).getLast? = some (SatGlobalVertexPlacement.actualPoint φ (target φ o b)) := by
  have h := SatClauseWireLattice.route_endpoints
    (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b
  cases b <;> simpa only [route,source,target,Bool.false_eq_true,ite_false,ite_true,
    actualPoint_clauseVertex,actualPoint_actualWireVertex] using h

theorem route_simple (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (route φ o b).Nodup ∧ (route φ o b).IsChain UnitStep :=
  SatClauseWireLattice.route_simple _ _ _

theorem route_length (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    65 ≤ (route φ o b).length ∧ (route φ o b).length ≤ 1536*m := by
  have h := SatClauseWireLattice.route_length_bound
    (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b
  change 65 ≤ (route φ o b).length ∧ (route φ o b).length ≤ 512*(3*m) at h
  omega

theorem route_bounds (φ : Formula n m) (o : Occurrence m) (b : Bool)
    (q : Point) (hq : q ∈ route φ o b) :
    -64 ≤ q.1 ∧ q.1 ≤ 1536*m-65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 3072*m+516 := by
  have h := SatClauseWireLattice.route_bounds
    (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b q hq
  push_cast at h
  omega

theorem pairwise_separation (φ : Formula n m) (o t : Occurrence m) (a b : Bool)
    (hne : (o, a) ≠ (t, b)) (q r : Point)
    (hq : q ∈ route φ o a) (hr : r ∈ route φ t b) :
    8 ≤ IntegerGrid.manhattan q r := by
  apply SatClauseWireLattice.pairwise_separation (SatClauseOrder.permutation φ)
    (SatWireLayout.variableRank φ o) (SatWireLayout.variableRank φ t) a b _ q r hq hr
  intro he
  have hot : o = t := (SatWireLayout.variableRank φ).injective (congrArg Prod.fst he)
  have hab : a = b := congrArg Prod.snd he
  exact hne (Prod.ext hot hab)

theorem routes_disjoint (φ : Formula n m) (o t : Occurrence m) (a b : Bool)
    (hne : (o, a) ≠ (t, b)) : (route φ o a).Disjoint (route φ t b) := by
  apply List.disjoint_left.mpr
  intro q hq hr
  have h := pairwise_separation φ o t a b hne q q hq hr
  simp [IntegerGrid.manhattan] at h

theorem body_vertex_clear (φ : Formula n m) (o : Occurrence m) (b : Bool)
    (v : PermutationWirePlacement.BodyVertex n m) :
    SatGlobalVertexPlacement.bodyPoint φ v ∈ route φ o b ↔
      v = .inr (.inr (o.1,clausePort o b)) := by
  constructor
  · intro h
    have hb := route_bounds φ o b _ h
    rcases v with i | ⟨v,a⟩ | ⟨c,v⟩
    · fin_cases i <;>
        dsimp [SatGlobalVertexPlacement.bodyPoint,SatExteriorLattice.sentinel,
          SatVariableLattice.wireX] at hb <;> omega
    · have hx := SatVariablePlacement.point_x φ v a
      change (SatVariablePlacement.point φ v a).1 = _ at hx
      dsimp [SatGlobalVertexPlacement.bodyPoint,SatVariableLattice.wireX] at hb hx
      omega
    · have hp := (clause_box_intersection φ o b c _ h
        (SatClauseOrder.point_in_box c v)).2
      have hv := SatClauseOrder.point_injective m
        (a₁ := (c,v)) (a₂ := (o.1,clausePort o b)) hp
      exact congrArg (fun z => Sum.inr (Sum.inr z)) hv
  · rintro rfl
    change SatClauseOrder.point o.1 (clausePort o b) ∈ _
    unfold clausePort
    rw [← clause_endpoint φ o b]
    rw [route,SatClauseWireLattice.route_mem]
    have hb := finishX_bounds (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o)
    exact ⟨rfl,le_rfl,by dsimp [clausePoint]; omega⟩

/-- Clearance is against every actual vertex of the final sweep graph,
not merely against the displayed clause and wire subfamilies. -/
theorem route_vertex_clear (φ : Formula n m) (o : Occurrence m) (b : Bool)
    (v : (SatClauseOrder.graph φ).Vertex) :
    SatGlobalVertexPlacement.actualPoint φ v ∈ route φ o b ↔
      v = source φ o b ∨ v = target φ o b := by
  constructor
  · intro h
    obtain ⟨z,rfl⟩ := (SatGlobalVertexPlacement.equiv φ).surjective v
    rw [SatGlobalVertexPlacement.actualPoint_equiv] at h
    cases z with
    | inl z =>
      have hz := (body_vertex_clear φ o b z).mp h
      subst z
      have he : SatGlobalVertexPlacement.equiv φ
          (.inl (.inr (.inr (o.1,clausePort o b)))) = clauseVertex φ o b := by
        rw [SatGlobalVertexPlacement.equiv_body]
        rfl
      cases b
      · exact Or.inl he
      · exact Or.inr he
    | inr z =>
      have hz := (wire_vertex_clear (SatClauseOrder.permutation φ)
        (SatWireLayout.variableRank φ o) b z).mp h
      subst z
      have he : SatGlobalVertexPlacement.equiv φ
          (.inr (wireVertex (SatClauseOrder.permutation φ)
            (SatWireLayout.variableRank φ o) b)) = actualWireVertex φ o b := by
        rw [SatGlobalVertexPlacement.equiv_wire]
        rfl
      cases b
      · exact Or.inr he
      · exact Or.inl he
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (route_endpoints φ o b).1
    · exact List.mem_of_getLast? (route_endpoints φ o b).2

end GridHardness.SatClauseWireDrawing
