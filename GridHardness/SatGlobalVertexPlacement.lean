/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalPermutationWirePlacement
public import GridHardness.SatClauseOrder
public import GridHardness.SatVariablePlacement
public import GridHardness.SatExteriorLattice

/-!
# SAT Global Vertex Placement

Simultaneous coordinates for every vertex of the reversed-block SAT
sweep graph. An explicit body-plus-wire equivalence accounts for every
actual vertex. Regularity is needed for injectivity of variable coordinates,
but not to define any coordinate. This is a vertex placement, not an edge
drawing or a grid-graph reduction.
-/

@[expose] public section

namespace GridHardness.SatGlobalVertexPlacement
open PlanarSatAssembly
open CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev BodyVertex := PermutationWirePlacement.BodyVertex
abbrev WireVertex {n m : Nat} (φ : Formula n m) :=
  SatCrossingWireVertices.Vertex (SatClauseOrder.permutation φ)
abbrev Vertex {n m : Nat} (φ : Formula n m) := BodyVertex n m ⊕ WireVertex φ
abbrev Names {n m : Nat} (φ : Formula n m) :=
  PlanarSatAssembly.Vertex n m ⊕
    (WireCrossingSchedule.Cell (SatClauseOrder.permutation φ) ×
      SatCrossingHorizontal.RetainedVertex)

variable {n m : Nat} (φ : Formula n m)

def names : Vertex φ → Names φ
  | .inl b => .inl (PermutationWirePlacement.bodyNames b)
  | .inr w => PermutationWirePlacement.names φ (SatClauseOrder.permutation φ) w

def decode : Names φ → Vertex φ
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr (.inl vb)) => .inl (.inr (.inl vb))
  | .inl (.inr (.inr (.inl cv))) => .inl (.inr (.inr cv))
  | .inl (.inr (.inr (.inr (o,v)))) => .inr (.inl (SatWireLayout.variableRank φ o,v))
  | .inr cv => .inr (.inr cv)

/-- Both directions inspect the actual finite vertex tags; no cardinality
enumeration or choice of unnamed vertices is used. -/
def namesEquiv : Vertex φ ≃ Names φ where
  toFun := names φ
  invFun := decode φ
  left_inv z := by
    rcases z with (i | ⟨v,b⟩ | ⟨c,v⟩) | (⟨j,v⟩ | ⟨c,v⟩)
    all_goals simp only [names,decode,PermutationWirePlacement.bodyNames,
      PermutationWirePlacement.names,sent,var,clause,PlanarSatAssembly.xor,
      Equiv.apply_symm_apply]
  right_inv z := by
    rcases z with (i | ⟨v,b⟩ | ⟨c,v⟩ | ⟨o,v⟩) | ⟨c,v⟩
    all_goals simp only [names,decode,PermutationWirePlacement.bodyNames,
      PermutationWirePlacement.names,sent,var,clause,PlanarSatAssembly.xor,
      Equiv.symm_apply_apply]

noncomputable def equiv : Vertex φ ≃ (SatClauseOrder.graph φ).Vertex :=
  (namesEquiv φ).trans
    (PermutationWirePlacement.decomposition φ (SatClauseOrder.permutation φ)).symm

theorem equiv_body (b : BodyVertex n m) :
    equiv φ (.inl b)=
      PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) b := by
  apply (PermutationWirePlacement.decomposition φ (SatClauseOrder.permutation φ)).injective
  change (PermutationWirePlacement.decomposition φ (SatClauseOrder.permutation φ))
    ((PermutationWirePlacement.decomposition φ (SatClauseOrder.permutation φ)).symm
      (.inl (PermutationWirePlacement.bodyNames b)))=_
  rw [Equiv.apply_symm_apply,PermutationWirePlacement.bodyVertex_names]

theorem equiv_wire (v : WireVertex φ) :
    equiv φ (.inr v)=PermutationWirePlacement.vertex φ (SatClauseOrder.permutation φ) v := rfl

def bodyPoint : BodyVertex n m → Point
  | .inl i => SatExteriorLattice.sentinel (3*m) i
  | .inr (.inl (v,b)) => SatVariablePlacement.point φ v b
  | .inr (.inr (c,v)) => SatClauseOrder.point c v

def point : Vertex φ → Point
  | .inl b => bodyPoint φ b
  | .inr w => SatCrossingWireVertices.point (SatClauseOrder.permutation φ) w

noncomputable def actualPoint (v : (SatClauseOrder.graph φ).Vertex) : Point :=
  point φ ((equiv φ).symm v)

theorem actualPoint_equiv (v : Vertex φ) : actualPoint φ (equiv φ v)=point φ v := by
  rw [actualPoint,Equiv.symm_apply_apply]

theorem actualPoint_body (b : BodyVertex n m) :
    actualPoint φ (PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) b)=
      bodyPoint φ b := by
  rw [← equiv_body,actualPoint_equiv]
  rfl

theorem actualPoint_wire (v : WireVertex φ) :
    actualPoint φ (PermutationWirePlacement.vertex φ (SatClauseOrder.permutation φ) v)=
      SatCrossingWireVertices.point (SatClauseOrder.permutation φ) v := by
  rw [← equiv_wire,actualPoint_equiv]
  rfl

theorem actualPoint_sentinel (i : Fin 3) :
    actualPoint φ (CorrectedSatInterval.PermutationGraph.liftOriginal φ
      (SatClauseOrder.permutation φ) (sent i))=SatExteriorLattice.sentinel (3*m) i :=
  actualPoint_body φ (.inl i)

theorem actualPoint_variable (v : Fin n) (b : Bool) :
    actualPoint φ (CorrectedSatInterval.PermutationGraph.liftOriginal φ
      (SatClauseOrder.permutation φ) (var v b))=SatVariablePlacement.point φ v b :=
  actualPoint_body φ (.inr (.inl (v,b)))

theorem actualPoint_clause (c : Fin m) (v : Fin 12) :
    actualPoint φ (SatClauseOrder.vertex φ c v)=SatClauseOrder.point c v :=
  actualPoint_body φ (.inr (.inr (c,v)))

theorem variable_y_lower (v : Fin n) (b : Bool) :
    128≤(SatVariablePlacement.point φ v b).2 := by
  have h := (SatVariablePlacement.point_between φ v b).1
  change 512*(SatVariableOrder.prefix φ v:Int)+128≤_ at h
  omega

theorem sentinel_injective (N : Nat) :
    Function.Injective (SatExteriorLattice.sentinel N) := by
  intro i j h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases i <;> fin_cases j <;> dsimp [SatExteriorLattice.sentinel,
    SatVariableLattice.wireX] at hx hy <;> first | rfl | omega

theorem sentinel_ne_variable (i : Fin 3) (v : Fin n) (b : Bool) :
    SatExteriorLattice.sentinel (3*m) i≠SatVariablePlacement.point φ v b := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hv := SatVariablePlacement.point_x φ v b
  have hb := variable_y_lower φ v b
  fin_cases i <;> dsimp [SatExteriorLattice.sentinel] at hx hy
  all_goals dsimp [SatVariableLattice.wireX] at hv; omega

theorem sentinel_ne_clause (i : Fin 3) (c : Fin m) (v : Fin 12) :
    SatExteriorLattice.sentinel (3*m) i≠SatClauseOrder.point c v := by
  intro h
  have hx := congrArg Prod.fst h
  have hb := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
  fin_cases i <;> dsimp [SatExteriorLattice.sentinel,SatVariableLattice.wireX] at hx
  all_goals omega

theorem variable_ne_clause (v : Fin n) (b : Bool) (c : Fin m) (w : Fin 12) :
    SatVariablePlacement.point φ v b≠SatClauseOrder.point c w := by
  intro h
  have hx := congrArg Prod.fst h
  have hv := SatVariablePlacement.point_x φ v b
  have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c w)
  dsimp [SatVariableLattice.wireX] at hv
  omega

theorem bodyPoint_injective (hφ : SatVariablePlacement.Regular φ) :
    Function.Injective (bodyPoint φ) := by
  intro u v h
  rcases u with i | ⟨u,a⟩ | ⟨c,u⟩ <;> rcases v with j | ⟨v,b⟩ | ⟨d,v⟩
  · exact congrArg Sum.inl (sentinel_injective (3*m) h)
  · exact False.elim (sentinel_ne_variable φ i v b h)
  · exact False.elim (sentinel_ne_clause i d v h)
  · exact False.elim (sentinel_ne_variable φ j u a h.symm)
  · exact congrArg (fun z => Sum.inr (Sum.inl z))
      (SatVariablePlacement.point_injective φ hφ (a₁:=(u,a)) (a₂:=(v,b)) h)
  · exact False.elim (variable_ne_clause φ u a d v h)
  · exact False.elim (sentinel_ne_clause j c u h.symm)
  · exact False.elim (variable_ne_clause φ v b c u h.symm)
  · exact congrArg (fun z => Sum.inr (Sum.inr z))
      (SatClauseOrder.point_injective m (a₁:=(c,u)) (a₂:=(d,v)) h)

theorem body_ne_wire (b : BodyVertex n m) (w : WireVertex φ) :
    bodyPoint φ b≠SatCrossingWireVertices.point (SatClauseOrder.permutation φ) w := by
  intro h
  have hw := SatCrossingWireVertices.point_bounds (SatClauseOrder.permutation φ) w
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  rcases b with i | ⟨v,b⟩ | ⟨c,v⟩
  · fin_cases i <;> dsimp [bodyPoint,SatExteriorLattice.sentinel,
      SatVariableLattice.wireX] at hx hy <;> omega
  · have hv := SatVariablePlacement.point_x φ v b
    change (SatVariablePlacement.point φ v b).1=_ at hx
    dsimp [SatVariableLattice.wireX] at hv
    omega
  · have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
    change (SatClauseOrder.point c v).1=_ at hx
    omega

theorem point_injective (hφ : SatVariablePlacement.Regular φ) :
    Function.Injective (point φ) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v
  · exact congrArg Sum.inl (bodyPoint_injective φ hφ h)
  · exact False.elim (body_ne_wire φ u v h)
  · exact False.elim (body_ne_wire φ v u h.symm)
  · exact congrArg Sum.inr (SatCrossingWireVertices.point_injective _ h)

theorem same_point_iff_same_vertex (hφ : SatVariablePlacement.Regular φ) (u v : Vertex φ) :
    point φ u=point φ v ↔ equiv φ u=equiv φ v := by
  constructor
  · intro h
    exact congrArg (equiv φ) (point_injective φ hφ h)
  · intro h
    exact congrArg (point φ) ((equiv φ).injective h)

theorem actualPoint_injective (hφ : SatVariablePlacement.Regular φ) :
    Function.Injective (actualPoint φ) :=
  (point_injective φ hφ).comp (equiv φ).symm.injective

theorem actualPoint_eq_iff (hφ : SatVariablePlacement.Regular φ)
    (u v : (SatClauseOrder.graph φ).Vertex) :
    actualPoint φ u=actualPoint φ v ↔ u=v :=
  ⟨fun h => actualPoint_injective φ hφ h,fun h => congrArg (actualPoint φ) h⟩

theorem point_bounds (v : Vertex φ) :
    -128≤(point φ v).1 ∧ (point φ v).1≤SatVariableLattice.wireX (3*m)+64 ∧
      -64≤(point φ v).2 ∧ (point φ v).2≤1024*(3*m:Int)+522 := by
  rcases v with (i | ⟨v,b⟩ | ⟨c,v⟩) | w
  · fin_cases i <;> dsimp [point,bodyPoint,SatExteriorLattice.sentinel,
      SatVariableLattice.wireX] <;> omega
  · have hv := SatVariablePlacement.point_bounds φ v b
    dsimp only [point,bodyPoint]
    dsimp [SatVariableLattice.wireX] at hv ⊢
    omega
  · have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
    dsimp only [point,bodyPoint]
    dsimp [SatVariableLattice.wireX]
    omega
  · have hw := SatCrossingWireVertices.point_bounds (SatClauseOrder.permutation φ) w
    dsimp only [point]
    dsimp [SatVariableLattice.wireX]
    omega

theorem actualPoint_bounds (v : (SatClauseOrder.graph φ).Vertex) :
    -128≤(actualPoint φ v).1 ∧ (actualPoint φ v).1≤SatVariableLattice.wireX (3*m)+64 ∧
      -64≤(actualPoint φ v).2 ∧ (actualPoint φ v).2≤1024*(3*m:Int)+522 :=
  point_bounds φ ((equiv φ).symm v)

/-- Every actual graph vertex receives one of the displayed coordinates. -/
theorem covers (v : (SatClauseOrder.graph φ).Vertex) :
    ∃ z : Vertex φ, equiv φ z=v ∧ point φ z=actualPoint φ v :=
  ⟨(equiv φ).symm v,(equiv φ).apply_symm_apply v,rfl⟩

theorem finite_actualPoint_injective (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) : Function.Injective (actualPoint (finiteFormula x)) :=
  actualPoint_injective (finiteFormula x) (SatVariablePlacement.finite_regular x hw)

end GridHardness.SatGlobalVertexPlacement
