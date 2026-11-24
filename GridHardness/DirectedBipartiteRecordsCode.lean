/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedIncidenceRecordCode
public import GridHardness.DirectedBipartitePlacementCode
public import GridHardness.LatticeRouteCoreCode

/-!
# Directed Bipartite Records Code

A polynomial compiler from explicit directed vertex and route records to
the point/phase and route/orientation records consumed by the layout backend.
The local selector receives incidences recovered from the directed routes.
Four vertices and three internal routes are emitted per old vertex; each
external route is subdivided at scale sixteen and trimmed by its chosen ports.
-/

@[expose] public section

namespace GridHardness.DirectedBipartiteRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open DirectedRouteLookupCode DirectedPortSelectionCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev VertexTy := Ty.pair .nat PointTy
abbrev InputTy := Ty.pair (.list VertexTy) RecordsTy
abbrev ClusterTy := Ty.pair PointTy .bool
abbrev RouteTy := Ty.pair CycleInputTy .bool
abbrev OutputTy := Ty.pair (.list ClusterTy) (.list RouteTy)
abbrev PlacedTy := DirectedBipartitePlacementCode.PlacedTy
abbrev LocalTy := Ty.pair RecordsTy VertexTy

def choice : Code (.pair RecordsTy .nat) PortTy :=
  .comp DirectedIncidenceRecordCode.code DirectedPortSelectionCode.code

def placed : Code LocalTy PlacedTy :=
  .pair (.comp .snd .snd) (.comp (.pair .fst (.comp .snd .fst)) choice)

/-- Odd path positions are the color-one vertices. Only positions zero
through three are emitted by the enclosing fixed-size map. -/
def phase : Code .nat .bool :=
  .comp (.pair (.comp (.pair .id (.const .nat 1)) .natEq)
    (.comp (.pair .id (.const .nat 3)) .natEq)) .boolOr

theorem phase_eval (i : Fin 4) : phase.eval i.val=decide (i.val%2=1) := by
  fin_cases i <;> rfl

def cluster : Code (.pair PlacedTy .nat) ClusterTy :=
  .pair DirectedBipartitePlacementCode.point (.comp .snd phase)

def localClusters : Code PlacedTy (.list ClusterTy) :=
  .comp (.pair .id (.const (.list .nat) [0,1,2,3])) (.listMapEnv cluster)

def internalRoute : Code (.pair PlacedTy .nat) RouteTy :=
  let next := .comp (.pair .fst (.comp (.pair .snd (.const .nat 1)) .natAdd))
    DirectedBipartitePlacementCode.point
  .pair (Code.append (.comp DirectedBipartitePlacementCode.point .listSingle)
    (.comp next .listSingle)) (.comp .snd phase)

def localInternal : Code PlacedTy (.list RouteTy) :=
  .comp (.pair .id (.const (.list .nat) [0,1,2])) (.listMapEnv internalRoute)

def externalRoute : Code (.pair RecordsTy RecordTy) RouteTy :=
  let src := .comp (.pair .fst (.comp (.comp .snd .fst) .fst)) choice
  let tgt := .comp (.pair .fst (.comp (.comp .snd .fst) .snd)) choice
  let radius := .comp (.pair tgt (.const .bool true)) DirectedBipartitePlacementCode.radius
  let data := .pair (.comp .snd .snd) radius
  .pair (.branch (.comp src .fst) (.comp data (coreCode 16 0))
    (.comp data (coreCode 16 3))) (.const .bool true)

def clusters : Code InputTy (.list ClusterTy) :=
  .comp (.pair .snd .fst) (.comp (.listMapEnv (.comp placed localClusters)) .listJoin)

def internalRoutes : Code InputTy (.list RouteTy) :=
  .comp (.pair .snd .fst) (.comp (.listMapEnv (.comp placed localInternal)) .listJoin)

def externalRoutes : Code InputTy (.list RouteTy) :=
  .comp (.pair .snd .snd) (.listMapEnv externalRoute)

def code : Code InputTy OutputTy :=
  .pair clusters (Code.append internalRoutes externalRoutes)

attribute [local irreducible] choice

theorem placed_eval (rs : RecordsTy.denote) (v : VertexTy.denote) :
    placed.eval (rs,v)=(v.2,choice.eval (rs,v.1)) := rfl

theorem cluster_eval (p : PointTy.denote) (c : DirectedPortSelection.Port) (i : Fin 4) :
    cluster.eval ((p,encodePort c),i.val)=
      (encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 i),decide (i.val%2=1)) := by
  change (DirectedBipartitePlacementCode.point.eval ((p,encodePort c),i.val),phase.eval i.val)=_
  rw [DirectedBipartitePlacementCode.point_eval,phase_eval]

theorem internalRoute_eval (p : PointTy.denote) (c : DirectedPortSelection.Port) (i : Fin 3) :
    internalRoute.eval ((p,encodePort c),i.val)=
      ([encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 i.castSucc),
        encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 i.succ)],decide (i.val%2=1)) := by
  change ([DirectedBipartitePlacementCode.point.eval ((p,encodePort c),i.val),
    DirectedBipartitePlacementCode.point.eval ((p,encodePort c),i.val+1)],phase.eval i.val)=_
  apply Prod.ext
  · exact congrArg₂ (fun a b => [a,b]) (DirectedBipartitePlacementCode.point_eval p c i.castSucc)
      (DirectedBipartitePlacementCode.point_eval p c i.succ)
  · exact phase_eval i.castSucc

theorem externalRoute_eval (rs : RecordsTy.denote) (r : RecordTy.denote)
    (c d : DirectedPortSelection.Port)
    (hc : choice.eval (rs, r.1.1) = encodePort c)
    (hd : choice.eval (rs, r.1.2) = encodePort d) :
    externalRoute.eval (rs,r)=
      ((LatticeRouteCore.core 16 (if false=c.1 then 3 else 0)
        (if true=d.1 then 3 else 0) (r.2.map decoded)).map encodePoint,true) := by
  change ((if (choice.eval (rs,r.1.1)).1 then
      (coreCode 16 0).eval (r.2,DirectedBipartitePlacementCode.radius.eval (choice.eval (rs,r.1.2),true))
    else (coreCode 16 3).eval (r.2,DirectedBipartitePlacementCode.radius.eval (choice.eval (rs,r.1.2),true))),true)=_
  rw [hc,hd,DirectedBipartitePlacementCode.radius_eval]
  rcases c with ⟨b,c⟩
  cases b <;> simp only [encodePort, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true]
  · rw [coreCode_eval]
  · rw [coreCode_eval]

attribute [local irreducible] cluster internalRoute

theorem mem_localClusters (p : PlacedTy.denote) (q : ClusterTy.denote) :
    q∈localClusters.eval p ↔ ∃i:Fin 4,q=cluster.eval (p,i.val) := by
  change q∈[cluster.eval (p,0),cluster.eval (p,1),cluster.eval (p,2),cluster.eval (p,3)] ↔ _
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
  · rintro ⟨i,h⟩
    fin_cases i <;> simp_all

theorem mem_localInternal (p : PlacedTy.denote) (q : RouteTy.denote) :
    q∈localInternal.eval p ↔ ∃i:Fin 3,q=internalRoute.eval (p,i.val) := by
  change q∈[internalRoute.eval (p,0),internalRoute.eval (p,1),internalRoute.eval (p,2)] ↔ _
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro (h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  · rintro ⟨i,h⟩
    fin_cases i <;> simp_all

attribute [local irreducible] placed localClusters localInternal externalRoute

theorem clusters_eval (vs : List VertexTy.denote) (rs : RecordsTy.denote) :
    clusters.eval (vs,rs)=vs.flatMap (fun v => localClusters.eval (placed.eval (rs,v))) := rfl

theorem internalRoutes_eval (vs : List VertexTy.denote) (rs : RecordsTy.denote) :
    internalRoutes.eval (vs,rs)=vs.flatMap (fun v => localInternal.eval (placed.eval (rs,v))) := rfl

theorem externalRoutes_eval (vs : List VertexTy.denote) (rs : RecordsTy.denote) :
    externalRoutes.eval (vs,rs)=rs.map (fun r => externalRoute.eval (rs,r)) := rfl

attribute [local irreducible] clusters internalRoutes externalRoutes

theorem code_eval (z : InputTy.denote) : code.eval z=
    (clusters.eval z,internalRoutes.eval z++externalRoutes.eval z) := rfl

end GridHardness.DirectedBipartiteRecordsCode
