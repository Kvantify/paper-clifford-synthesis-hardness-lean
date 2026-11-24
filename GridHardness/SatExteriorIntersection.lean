/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorDrawing
public import GridHardness.SatExteriorSeparation

/-!
# SAT Exterior Intersection

The complete exterior family intersects only at its shared sentinel
endpoints. The nonempty and empty closing cases belong to one edge family.
-/

@[expose] public section

namespace GridHardness.SatExteriorDrawing
open CliffordComplexity PlanarSatAssembly
open SatExteriorLattice SatExteriorSeparation
set_option autoImplicit false

def Incident (x : SatTy.denote) (e : Edge x.length) (q : Int × Int) : Prop :=
  q=SatGlobalVertexPlacement.bodyPoint (finiteFormula x) (source x e) ∨
  q=SatGlobalVertexPlacement.bodyPoint (finiteFormula x) (target x e)

private def index {m : Nat} : Edge m → Nat
  | .sentinelFirst => 0
  | .sentinelSecond => 1
  | .firstVariable => 2
  | .forward _ => 3
  | .returning _ => 4
  | .closing _ => 5

private theorem index_injective {m : Nat} : Function.Injective (@index m) := by
  intro e f h
  cases e <;> cases f <;> simp_all [index]

private theorem intersection_ordered (x : SatTy.denote) (e f : Edge x.length)
    (hlt : index e < index f) (q : Int × Int) (he : q ∈route x e) (hf : q ∈route x f) :
    Incident x e q ∧ Incident x f q := by
  cases e <;> cases f <;> simp only [index] at hlt
  all_goals try omega
  all_goals simp only [route] at he hf
  case sentinelFirst.sentinelSecond =>
    have hq := down_bottom_intersection (3*x.length) q he hf
    simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint,hq]
  case sentinelFirst.firstVariable =>
    exact False.elim (List.disjoint_left.mp (down_firstVariable_disjoint (3*x.length)) he hf)
  case sentinelFirst.forward =>
    exact False.elim ((forward_sentinel_clear (3*x.length) q hf).1 he)
  case sentinelFirst.returning =>
    have hq := returning_down_intersection (3*x.length) q hf he
    simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint,hq]
  case sentinelFirst.closing h =>
    have hq := closing_down_intersection q hf he
    simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint,hq,sentinel]
  case sentinelSecond.firstVariable =>
    have hq := bottom_firstVariable_intersection (3*x.length) q he hf
    simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint,hq]
  case sentinelSecond.forward =>
    exact False.elim ((forward_sentinel_clear (3*x.length) q hf).2.1 he)
  case sentinelSecond.returning =>
    exact False.elim (List.disjoint_left.mp (returning_bottom_disjoint (3*x.length)) hf he)
  case sentinelSecond.closing h =>
    simp only [h,Nat.mul_zero] at he
    exact False.elim (List.disjoint_left.mp closing_bottom_disjoint hf he)
  case firstVariable.forward =>
    exact False.elim ((forward_sentinel_clear (3*x.length) q hf).2.2 he)
  case firstVariable.returning =>
    exact False.elim (List.disjoint_left.mp (returning_firstVariable_disjoint (3*x.length)) hf he)
  case firstVariable.closing h =>
    simp only [h,Nat.mul_zero] at he
    exact False.elim (List.disjoint_left.mp closing_firstVariable_disjoint hf he)
  case forward.returning hm _ =>
    exact False.elim (List.disjoint_left.mp (forward_returning_disjoint x.length hm) he hf)

theorem route_intersection (x : SatTy.denote) (e f : Edge x.length) (hne : e ≠f)
    (q : Int × Int) (he : q ∈route x e) (hf : q ∈route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases lt_trichotomy (index e) (index f) with h | h | h
  · exact intersection_ordered x e f h q he hf
  · exact False.elim (hne (index_injective h))
  · exact (intersection_ordered x f e h q hf he).symm

theorem actual_route_intersection (x : SatTy.denote) (e f : Edge x.length) (hne : e ≠f)
    (q : Int × Int) (he : q ∈route x e) (hf : q ∈route x f) :
    (q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (sourceVertex x e) ∨
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (targetVertex x e)) ∧
    (q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (sourceVertex x f) ∨
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (targetVertex x f)) := by
  simp only [sourceVertex,targetVertex,SatGlobalVertexPlacement.actualPoint_body]
  exact route_intersection x e f hne q he hf

end GridHardness.SatExteriorDrawing
