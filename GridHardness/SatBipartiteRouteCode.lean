/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.BipartiteRouteDataCode
public import GridHardness.SatCompleteTentacleCode

/-!
# SAT Bipartite Route Code

An actual SAT tentacle compiler beginning at the original bipartite route.
All orientation, dilation, endpoint cuts, owner state, receiving data, signed
strips and collar selection are executed. `SatDirectedRecordsCode` and
`SatBipartiteRecordsCode` generate the original route from SAT.
-/

@[expose] public section

namespace GridHardness.SatBipartiteRouteCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
open BipartiteRouteDataCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

noncomputable def input (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    BipartiteRouteDataCode.InputTy.denote :=
  ((SatBipartiteDrawing.route x hw e).map encodePoint,SatDockCorridors.reverseEdge x e)

theorem oriented_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    oriented.eval (input x hw e)=(SatDockCorridors.original x hw e).map encodePoint := by
  change (orientCode PointTy).eval ((SatBipartiteDrawing.route x hw e).map encodePoint,
    SatDockCorridors.reverseEdge x e)=_
  rw [orientCode_eval]
  cases h : SatDockCorridors.reverseEdge x e <;>
    simp [SatDockCorridors.original,LatticeRouteDirections.orient,h,List.map_reverse]

theorem point_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) (b : Bool) :
    (point b).eval (input x hw e)=
      encodePoint (SatBipartiteDrawing.point x hw (SatDockCorridors.endpointVertex x e b)) := by
  change endpointPointCode.eval (oriented.eval (input x hw e),b)=_
  rw [oriented_eval,endpointPointCode_encoded _ b (SatDockCorridors.original_certificate x hw e).2.2.1,
    SatDockCorridors.original_endpoint]

theorem direction_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) (b : Bool) :
    (direction b).eval (input x hw e)=(SatDockCorridors.direction x hw e b).val := by
  change endpointDirectionCode.eval (oriented.eval (input x hw e),b)=_
  rw [oriented_eval,endpointDirectionCode_encoded _ b (SatDockCorridors.original_certificate x hw e).2.2.1,
    SatDockCorridors.original_direction]

theorem side_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) (b : Bool) :
    (side b).eval (input x hw e)=(SatDockCorridors.side x hw e b).val := by
  change sideCode.eval ((direction b).eval (input x hw e))=_
  rw [direction_eval,sideCode_eval]
  rfl

theorem ownerFrame_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    ownerFrame.eval (input x hw e)=encodeFrame
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)) := by
  change NineClusterCode.frame.eval (64,(point false).eval (input x hw e),false)=_
  rw [point_eval]
  change NineClusterCode.frame.eval (64,encodePoint
    (SatBipartiteDrawing.point x hw (SatDockCorridors.endpointVertex x e false)),
    decide ((0 : Fin 2)=1))=_
  rw [NineClusterCode.frame_eval 64 _ 0,GridAssembly.Encoding.decode_encode]
  congr 1
  unfold SatNineClusterPlacement.frame
  rw [SatOwnerTentacles.owner_color]
  rfl

theorem ownerState_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    ownerState.eval (input x hw e)=SignedRunCode.encodeState (SatOwnerTentacles.state x hw e) := by
  change NineClusterOwnerCode.state.eval (ownerFrame.eval (input x hw e),
    (side false).eval (input x hw e))=_
  rw [ownerFrame_eval,side_eval,NineClusterOwnerCode.state_eval,decode_encodeFrame]
  rfl

theorem recipientAnchor_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    recipientAnchor.eval (input x hw e)=encodePoint (SatCompleteTentacles.anchor x hw e) := by
  change (scalePointCode 64).eval ((point true).eval (input x hw e))=_
  rw [point_eval,scalePointCode_eval,GridAssembly.Encoding.decode_encode]
  rfl

theorem cut_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    cut.eval (input x hw e)=SatDockCorridors.endCut x hw e := by
  change endCutCode.eval ((side true).eval (input x hw e))=_
  rw [side_eval,endCutCode_eval]
  rfl

theorem corridor_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    corridor.eval (input x hw e)=(SatDockCorridors.route x hw e).map encodePoint := by
  change (coreCode 64 2).eval (oriented.eval (input x hw e),cut.eval (input x hw e))=_
  rw [oriented_eval,cut_eval,coreCode_encoded]
  rfl

/-- Every field of the complete-tentacle input is computed. -/
theorem data_eval (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    BipartiteRouteDataCode.code.eval (input x hw e)=SatCompleteTentacleCode.input x hw e := by
  change ((ownerState.eval (input x hw e),corridor.eval (input x hw e)),
    recipientAnchor.eval (input x hw e),(side true).eval (input x hw e))=_
  rw [ownerState_eval,corridor_eval,recipientAnchor_eval,side_eval]
  rfl

def code : Code BipartiteRouteDataCode.InputTy GridPointCode.InputTy :=
  .comp BipartiteRouteDataCode.code SatCompleteTentacleCode.code

noncomputable def rectangles (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : SatDockCorridors.Edge x) : GridPointCode.InputTy.denote := code.eval (input x hw e)

theorem rectangles_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    rectangles x hw e=SatCompleteTentacleCode.rectangles x hw e := by
  change SatCompleteTentacleCode.code.eval (BipartiteRouteDataCode.code.eval (input x hw e))=_
  rw [data_eval]
  rfl

theorem points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    GridPointCode.points (rectangles x hw e)=(SatCompleteTentacles.drawing x hw e).points := by
  rw [rectangles_eq,SatCompleteTentacleCode.points]

end GridHardness.SatBipartiteRouteCode
