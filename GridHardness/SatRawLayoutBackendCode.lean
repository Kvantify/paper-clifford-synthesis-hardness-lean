/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteRouteCode
public import GridHardness.SatLayoutBackendCode

/-!
# SAT Raw Layout Backend Code

A full layout compiler starting with the bipartite drawing's signed point
and route records. Cluster frames, owner states, oriented and trimmed corridors,
all signed strips, recipient collars, and final rectangle assembly are computed.
Generating the original drawing records from SAT is performed by `SatDirectedRecordsCode`.
-/

@[expose] public section

namespace GridHardness.SatRawLayoutBackendCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

abbrev ClusterTy := Ty.pair PointTy .bool
abbrev InputTy := Ty.pair (.list ClusterTy) (.list BipartiteRouteDataCode.InputTy)

def frame : Code ClusterTy FrameTy :=
  .comp (.pair (.const .nat 64) .id) NineClusterCode.frame

def prepare : Code InputTy SatLayoutBackendCode.InputTy :=
  .pair (.comp .fst (.listMap frame)) (.comp .snd (.listMap BipartiteRouteDataCode.code))

def code : Code InputTy GridPointCode.InputTy := .comp prepare SatLayoutBackendCode.code

noncomputable def clusters (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : List ClusterTy.denote :=
  FiniteRecordLists.records (fun v : SatBipartiteDrawing.Vertex x =>
    (encodePoint (SatBipartiteDrawing.point x hw v),decide (SatNineClusterPlacement.color x v=1)))

noncomputable def edges (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    List BipartiteRouteDataCode.InputTy.denote :=
  FiniteRecordLists.records (SatBipartiteRouteCode.input x hw)

noncomputable def input (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : InputTy.denote :=
  (clusters x hw,edges x hw)

private theorem map_records_eq {C : Type} [Fintype C] {σ τ : Ty}
    (f : C → σ.denote) (g : σ.denote → τ.denote) (h : C → τ.denote)
    (he : ∀ c, g (f c) =h c) :
    (FiniteRecordLists.records f).map g=FiniteRecordLists.records h := by
  unfold FiniteRecordLists.records
  rw [List.map_ofFn]
  congr 1
  funext i
  exact he _

theorem frame_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : SatBipartiteDrawing.Vertex x) :
    frame.eval (encodePoint (SatBipartiteDrawing.point x hw v),
      decide (SatNineClusterPlacement.color x v=1))=
      encodeFrame (SatNineClusterPlacement.frame x hw v) := by
  change NineClusterCode.frame.eval (64,encodePoint (SatBipartiteDrawing.point x hw v),
    decide (SatNineClusterPlacement.color x v=1))=_
  rw [NineClusterCode.frame_eval,GridAssembly.Encoding.decode_encode]
  rfl

/-- All layout-backend inputs are produced literally, not just up to
point-set equality or a change of vertex order. -/
theorem prepare_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    prepare.eval (input x hw)=SatLayoutBackendCode.input x hw := by
  change ((clusters x hw).map frame.eval,(edges x hw).map BipartiteRouteDataCode.code.eval)=_
  apply Prod.ext
  · exact map_records_eq (σ:=ClusterTy) (τ:=FrameTy) (fun v : SatBipartiteDrawing.Vertex x =>
      (encodePoint (SatBipartiteDrawing.point x hw v),
        decide (SatNineClusterPlacement.color x v=1))) frame.eval
      (fun v => encodeFrame (SatNineClusterPlacement.frame x hw v)) (frame_eval x hw)
  · exact map_records_eq (σ:=BipartiteRouteDataCode.InputTy) (τ:=SatCompleteTentacleCode.InputTy)
      (SatBipartiteRouteCode.input x hw) BipartiteRouteDataCode.code.eval
      (SatCompleteTentacleCode.input x hw) (SatBipartiteRouteCode.data_eval x hw)

noncomputable def rectangles (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    GridPointCode.InputTy.denote := code.eval (input x hw)

theorem rectangles_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    rectangles x hw=SatLayoutBackendCode.rectangles x hw := by
  change SatLayoutBackendCode.code.eval (prepare.eval (input x hw))=_
  rw [prepare_eval]
  rfl

theorem points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    GridPointCode.points (rectangles x hw)=(SatCompleteLayout.layout x hw).points := by
  rw [rectangles_eq,SatLayoutBackendCode.points]

end GridHardness.SatRawLayoutBackendCode
