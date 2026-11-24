/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatGlobalVertexPlacement
public import GridHardness.CorrectedSatIntervalExteriorCoreEdges

/-!
# SAT Exterior Drawing

Attach the exterior lattice paths to actual vertices of the finite
SAT sweep. Width-three syntax supplies the extra unused last variable;
the empty formula uses a separate closing route and no clause vertices.
-/

@[expose] public section

namespace GridHardness.SatExteriorDrawing
open CliffordComplexity PlanarSatAssembly
open CorrectedSatInterval CorrectedSatInterval.PermutationGraph.CoreEdges
open SatExteriorLattice
set_option autoImplicit false

def firstVar (x : SatTy.denote) : Fin ((vsOf x).length+1) := Exterior.first (by omega)
def lastVar (x : SatTy.denote) : Fin ((vsOf x).length+1) := Exterior.last (by omega)

theorem lastVar_eq (x : SatTy.denote) : lastVar x=SatVariableOrder.Finite.lastSlot x := by
  apply Fin.ext
  simp [lastVar,Exterior.last,SatVariableOrder.Finite.lastSlot]

theorem first_var_point (x : SatTy.denote) :
    SatVariablePlacement.point (finiteFormula x) (firstVar x) false=
      SatVariableLattice.entry (3*x.length) 0 := by
  simp [SatVariablePlacement.point,SatVariableOrder.prefix,firstVar,Exterior.first]

theorem last_var_point (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    SatVariablePlacement.point (finiteFormula x) (lastVar x) true=
      SatVariableLattice.emptyExit (3*x.length) (3*x.length) := by
  rw [lastVar_eq]
  simp only [SatVariablePlacement.point,SatVariableOrder.Finite.count_last_zero x hw,
    ite_true,SatVariableOrder.Finite.last_prefix x hw]

theorem first_clause_point {m : Nat} (hm : 0 <m) :
    SatClauseOrder.point (Exterior.first hm) 8=clauseEntry (3*m) := by
  rw [(SatClauseOrder.backbone_ports _).1,SatClauseOrder.base_eq]
  apply Prod.ext <;> dsimp [clauseEntry,Exterior.first]
  all_goals omega

theorem last_clause_point {m : Nat} (hm : 0 <m) :
    SatClauseOrder.point (Exterior.last hm) 1=clauseExit (3*m) := by
  rw [(SatClauseOrder.backbone_ports _).2,SatClauseOrder.base_eq]
  apply Prod.ext <;> dsimp [clauseExit,Exterior.last]
  all_goals omega

inductive Edge (m : Nat) where
  | sentinelFirst
  | sentinelSecond
  | firstVariable
  | forward (nonempty : 0<m)
  | returning (nonempty : 0<m)
  | closing (empty : m=0)

def source (x : SatTy.denote) : Edge x.length →
    PermutationWirePlacement.BodyVertex ((vsOf x).length+1) x.length
  | .sentinelFirst => .inl 0
  | .sentinelSecond => .inl 1
  | .firstVariable => .inl 2
  | .forward _ => .inr (.inl (lastVar x,true))
  | .returning h => .inr (.inr (Exterior.last h,1))
  | .closing _ => .inr (.inl (lastVar x,true))

def target (x : SatTy.denote) : Edge x.length →
    PermutationWirePlacement.BodyVertex ((vsOf x).length+1) x.length
  | .sentinelFirst => .inl 1
  | .sentinelSecond => .inl 2
  | .firstVariable => .inr (.inl (firstVar x,false))
  | .forward h => .inr (.inr (Exterior.first h,8))
  | .returning _ => .inl 0
  | .closing _ => .inl 0

def route (x : SatTy.denote) : Edge x.length → List (Int × Int)
  | .sentinelFirst => down
  | .sentinelSecond => bottom (3*x.length)
  | .firstVariable => SatExteriorLattice.firstVariable (3*x.length)
  | .forward _ => SatExteriorLattice.forward (3*x.length)
  | .returning _ => SatExteriorLattice.returning (3*x.length)
  | .closing _ => SatExteriorLattice.closing

noncomputable def sourceVertex (x : SatTy.denote) (e : Edge x.length) :
    (SatClauseOrder.graph (finiteFormula x)).Vertex :=
  PermutationWirePlacement.bodyVertex (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) (source x e)

noncomputable def targetVertex (x : SatTy.denote) (e : Edge x.length) :
    (SatClauseOrder.graph (finiteFormula x)).Vertex :=
  PermutationWirePlacement.bodyVertex (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) (target x e)

/-- Each listed route connects an edge of the actual completed graph;
source backbone membership is derived internally. -/
theorem edge_is_arc (x : SatTy.denote) (e : Edge x.length) :
    (SatClauseOrder.graph (finiteFormula x)).adj (sourceVertex x e) (targetVertex x e) := by
  cases e with
  | sentinelFirst => exact Exterior.sentinel_first _ _
  | sentinelSecond => exact Exterior.sentinel_second _ _
  | firstVariable => exact Exterior.sentinel_variable _ _ (by omega)
  | forward h => exact Exterior.variable_clause _ _ (by omega) h
  | returning h => exact Exterior.clause_sentinel _ _ h
  | closing h =>
    have hx : x=[] := List.length_eq_zero_iff.mp h
    subst x
    exact Exterior.variable_sentinel _ _ (by omega)

/-- Both endpoints use the single coordinate map of all final vertices. -/
theorem route_endpoints (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x.length) :
    (route x e).head?=some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (sourceVertex x e)) ∧
    (route x e).getLast?=some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (targetVertex x e)) := by
  simp only [sourceVertex,targetVertex,SatGlobalVertexPlacement.actualPoint_body]
  cases e with
  | sentinelFirst => exact ⟨(sentinel_endpoints (3*x.length)).1,
      (sentinel_endpoints (3*x.length)).2.1⟩
  | sentinelSecond => exact (sentinel_endpoints (3*x.length)).2.2
  | firstVariable =>
    change (SatExteriorLattice.firstVariable (3*x.length)).head?=some (sentinel (3*x.length) 2) ∧
      (SatExteriorLattice.firstVariable (3*x.length)).getLast?=
        some (SatVariablePlacement.point (finiteFormula x) (firstVar x) false)
    rw [first_var_point]
    exact ⟨(firstVariable_certificate _).1,(firstVariable_certificate _).2.1⟩
  | forward h =>
    change (SatExteriorLattice.forward (3*x.length)).head?=
      some (SatVariablePlacement.point (finiteFormula x) (lastVar x) true) ∧
      (SatExteriorLattice.forward (3*x.length)).getLast?=some (SatClauseOrder.point (Exterior.first h) 8)
    rw [last_var_point x hw,first_clause_point]
    exact forward_endpoints _
  | returning h =>
    change (SatExteriorLattice.returning (3*x.length)).head?=some (SatClauseOrder.point (Exterior.last h) 1) ∧
      (SatExteriorLattice.returning (3*x.length)).getLast?=some (sentinel (3*x.length) 0)
    rw [last_clause_point]
    exact returning_endpoints _
  | closing h =>
    change closing.head?=some (SatVariablePlacement.point (finiteFormula x) (lastVar x) true) ∧
      closing.getLast?=some (sentinel (3*x.length) 0)
    rw [last_var_point x hw,h]
    exact closing_endpoints

theorem route_simple (x : SatTy.denote) (e : Edge x.length) :
    (route x e).Nodup ∧ (route x e).IsChain UnitStep := by
  cases e with
  | sentinelFirst => exact down_simple
  | sentinelSecond => exact bottom_simple _
  | firstVariable =>
    exact ⟨(firstVariable_certificate _).2.2.1,(firstVariable_certificate _).2.2.2.1⟩
  | forward _ => exact forward_simple _
  | returning _ => exact returning_simple _
  | closing _ => exact closing_simple

theorem route_length_bound (x : SatTy.denote) (e : Edge x.length) :
    2≤(route x e).length ∧ (route x e).length≤4096*(x.length+1) := by
  cases e with
  | sentinelFirst => simp [route,down]; omega
  | sentinelSecond => simp [route,bottom]; omega
  | firstVariable =>
    have h := (firstVariable_certificate (3*x.length)).2.2.2.2
    change 2≤(SatExteriorLattice.firstVariable (3*x.length)).length ∧
      (SatExteriorLattice.firstVariable (3*x.length)).length≤_
    omega
  | forward _ => simp only [route,forward_length]; omega
  | returning _ => simp only [route,returning_length]; omega
  | closing _ => simp only [route,closing_length]; omega

end GridHardness.SatExteriorDrawing
