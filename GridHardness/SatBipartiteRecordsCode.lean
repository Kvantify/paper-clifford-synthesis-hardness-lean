/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedBipartiteRecordsCode
public import GridHardness.SatDirectedIncidenceCode
public import GridHardness.SatRawLayoutBackendCoverage

/-!
# SAT Bipartite Records Code

The explicit directed-record compiler produces precisely the cluster and
edge records of the actual SAT bipartite drawing. Completeness is stated as
record membership, so no canonical finite enumeration or duplicate-freeness
is required. Constructing the supplied directed records from SAT is separate.
-/

@[expose] public section

namespace GridHardness.SatBipartiteRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open SatCompleteDrawing DirectedPortSelectionCode DirectedBipartiteRecordsCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

variable (x : SatTy.denote) (label : Vertex x → Nat)

noncomputable def vertexRecord (v : Vertex x) : VertexTy.denote :=
  (label v,encodePoint (SatCompleteDrawing.point x v))

noncomputable def input (vs : List (Vertex x)) (arcs : List (Arc x)) :
    DirectedBipartiteRecordsCode.InputTy.denote :=
  (vs.map (vertexRecord x label),SatDirectedRouteLookupCode.records x label arcs)

variable (hw : ∀ c∈x, c.length =3) (hl : Function.Injective label)
  (arcs : List (Arc x)) (ha : ∀ a, a∈arcs)

noncomputable def chosen (v : Vertex x) : DirectedPortSelection.Port :=
  ((SatBipartitePorts.choose x hw v).incoming,(SatBipartitePorts.choose x hw v).direction)

attribute [local irreducible] DirectedBipartiteRecordsCode.choice

include hl ha in
theorem choice_actual (v : Vertex x) :
    DirectedBipartiteRecordsCode.choice.eval
      (SatDirectedRouteLookupCode.records x label arcs,label v)=encodePort (chosen x hw v) := by
  unfold DirectedBipartiteRecordsCode.choice
  exact SatDirectedIncidenceCode.selector x hw label hl arcs ha v

include hl ha in
theorem placed_actual (v : Vertex x) :
    placed.eval (SatDirectedRouteLookupCode.records x label arcs,vertexRecord x label v)=
      (encodePoint (SatCompleteDrawing.point x v),encodePort (chosen x hw v)) := by
  rw [placed_eval]
  exact congrArg (fun c => (encodePoint (SatCompleteDrawing.point x v),c))
    (choice_actual x label hw hl arcs ha v)

include hl ha in
theorem cluster_actual (v : Vertex x) (i : Fin 4) :
    cluster.eval (placed.eval (SatDirectedRouteLookupCode.records x label arcs,
      vertexRecord x label v),i.val)=
      (encodePoint (SatBipartiteDrawing.point x hw (v,i)),
        decide (SatNineClusterPlacement.color x (v,i)=1)) := by
  rw [placed_actual x label hw hl arcs ha,cluster_eval,GridAssembly.Encoding.decode_encode]
  apply Prod.ext
  · rfl
  · simp only [Fin.ext_iff,SatNineClusterPlacement.color_val,Fin.val_one]

/-- In the path of four vertices, precisely the middle internal route must
be reversed to begin at its color-zero endpoint. -/
theorem internal_reverse (v : Vertex x) (i : Fin 3) :
    SatDockCorridors.reverseEdge x (.inl (v,i))=decide (i.val%2=1) := by
  change (!decide (SatNineClusterPlacement.color x (v,i.castSucc)=0))=_
  simp only [Fin.ext_iff,SatNineClusterPlacement.color_val,Fin.val_zero,Fin.val_castSucc]
  fin_cases i <;> rfl

theorem external_reverse (a : Arc x) : SatDockCorridors.reverseEdge x (.inr a)=true := by
  change (!decide (SatNineClusterPlacement.color x (source x a,3)=0))=true
  simp only [Fin.ext_iff,SatNineClusterPlacement.color_val]
  rfl

include hl ha in
theorem internal_actual (v : Vertex x) (i : Fin 3) :
    internalRoute.eval (placed.eval (SatDirectedRouteLookupCode.records x label arcs,
      vertexRecord x label v),i.val)=SatBipartiteRouteCode.input x hw (.inl (v,i)) := by
  rw [placed_actual x label hw hl arcs ha,internalRoute_eval,GridAssembly.Encoding.decode_encode]
  change (_,decide (i.val%2=1))=
    ([encodePoint (SatBipartiteDrawing.point x hw (v,i.castSucc)),
      encodePoint (SatBipartiteDrawing.point x hw (v,i.succ))],SatDockCorridors.reverseEdge x (.inl (v,i)))
  rw [internal_reverse]
  rfl

include hl ha in
theorem external_actual (a : Arc x) :
    externalRoute.eval (SatDirectedRouteLookupCode.records x label arcs,
      SatDirectedRouteLookupCode.record x label a)=SatBipartiteRouteCode.input x hw (.inr a) := by
  rw [externalRoute_eval _ _ (chosen x hw (source x a)) (chosen x hw (target x a))
    (choice_actual x label hw hl arcs ha (source x a))
    (choice_actual x label hw hl arcs ha (target x a))]
  have hd : ((route x a).map encodePoint).map decoded=route x a := by
    rw [List.map_map]
    simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
    exact List.map_id _
  change ((LatticeRouteCore.core 16 _ _ (((route x a).map encodePoint).map decoded)).map encodePoint,true)=_
  rw [hd]
  change (_,true)=((SatBipartiteRoutes.route x hw a).map encodePoint,
    SatDockCorridors.reverseEdge x (.inr a))
  rw [external_reverse]
  rfl

attribute [local irreducible] placed cluster internalRoute externalRoute

include hl ha in
theorem clusters_coverage (vs : List (Vertex x)) (hv : ∀ v, v∈vs) (p : ClusterTy.denote) :
    p∈clusters.eval (input x label vs arcs) ↔ ∃v:SatBipartiteDrawing.Vertex x,
      p=(encodePoint (SatBipartiteDrawing.point x hw v),decide (SatNineClusterPlacement.color x v=1)) := by
  rw [clusters_eval]
  simp only [input,List.mem_flatMap]
  constructor
  · rintro ⟨r,hr,hp⟩
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,hi⟩ := (mem_localClusters _ p).mp hp
    exact ⟨(v,i),hi.trans (cluster_actual x label hw hl arcs ha v i)⟩
  · rintro ⟨⟨v,i⟩,rfl⟩
    refine ⟨vertexRecord x label v,List.mem_map_of_mem (hv v),?_⟩
    exact (mem_localClusters _ _).mpr ⟨i,(cluster_actual x label hw hl arcs ha v i).symm⟩

include hl ha in
theorem routes_coverage (vs : List (Vertex x)) (hv : ∀ v, v∈vs) (r : RouteTy.denote) :
    r∈internalRoutes.eval (input x label vs arcs)++externalRoutes.eval (input x label vs arcs) ↔
      ∃e:SatBipartiteDrawing.Edge x,r=SatBipartiteRouteCode.input x hw e := by
  rw [List.mem_append,internalRoutes_eval,externalRoutes_eval]
  simp only [input,List.mem_flatMap]
  constructor
  · rintro (⟨v,hv',hr⟩|hr)
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv'
      obtain ⟨i,hi⟩ := (mem_localInternal _ r).mp hr
      exact ⟨.inl (v,i),hi.trans (internal_actual x label hw hl arcs ha v i)⟩
    · obtain ⟨a,ha',hr⟩ := List.mem_map.mp hr
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha'
      exact ⟨.inr a,hr.symm.trans (external_actual x label hw hl arcs ha a)⟩
  · rintro ⟨e,rfl⟩
    cases e with
    | inl vi =>
      rcases vi with ⟨v,i⟩
      left
      refine ⟨vertexRecord x label v,List.mem_map_of_mem (hv v),?_⟩
      exact (mem_localInternal _ _).mpr ⟨i,(internal_actual x label hw hl arcs ha v i).symm⟩
    | inr a =>
      right
      exact List.mem_map.mpr ⟨SatDirectedRouteLookupCode.record x label a,
        List.mem_map_of_mem (ha a),external_actual x label hw hl arcs ha a⟩

/-- The actual raw-backend input type agrees literally with this compiler's
output: no extra geometric preprocessing is hidden at the composition point. -/
def code : Code DirectedBipartiteRecordsCode.InputTy GridPointCode.InputTy :=
  .comp DirectedBipartiteRecordsCode.code SatRawLayoutBackendCode.code

include hl ha in
theorem points (vs : List (Vertex x)) (hv : ∀ v, v∈vs) :
    GridPointCode.points (code.eval (input x label vs arcs))=(SatCompleteLayout.layout x hw).points := by
  change GridPointCode.points (SatRawLayoutBackendCode.code.eval
    (DirectedBipartiteRecordsCode.code.eval (input x label vs arcs)))=_
  apply SatRawLayoutBackendCode.points_of_coverage x hw
  · rw [DirectedBipartiteRecordsCode.code_eval]
    exact clusters_coverage x label hw hl arcs ha vs hv
  · rw [DirectedBipartiteRecordsCode.code_eval]
    exact routes_coverage x label hw hl arcs ha vs hv

end GridHardness.SatBipartiteRecordsCode
