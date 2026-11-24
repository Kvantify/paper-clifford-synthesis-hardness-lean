/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteEndpointCode
public import GridHardness.LatticeRouteCoreCode
public import GridHardness.NineClusterCode
public import GridHardness.NineClusterOwnerCode

/-!
# Bipartite Route Data Code

Derive all tentacle construction records from one bipartite route and
its owner-orientation bit. Endpoint coordinates, incidence sides, cluster
frame, tracked owner lane, receiving anchor, and asymmetric cuts are computed.
-/

@[expose] public section

namespace GridHardness.BipartiteRouteDataCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair CycleInputTy .bool

def sideCode : Code .nat .nat :=
  .branch (.comp (.pair .id (.const .nat 0)) .natEq) (.const .nat 2)
    (.branch (.comp (.pair .id (.const .nat 1)) .natEq) (.const .nat 3)
      (.branch (.comp (.pair .id (.const .nat 2)) .natEq) (.const .nat 0) (.const .nat 1)))

theorem sideCode_eval (d : Fin 4) :
    sideCode.eval d.val=(NineClusterDockGeometry.sideOfDirection d).val := by
  fin_cases d <;> rfl

def endCutCode : Code .nat .nat :=
  .branch (.comp (.pair .id (.const .nat 0)) .natEq) (.const .nat 8)
    (.branch (.comp (.pair .id (.const .nat 2)) .natEq) (.const .nat 10) (.const .nat 9))

theorem endCutCode_eval (s : Fin 4) : endCutCode.eval s.val=![8,9,10,9] s := by
  fin_cases s <;> rfl

def oriented : Code InputTy CycleInputTy := orientCode PointTy

def point (b : Bool) : Code InputTy PointTy :=
  .comp (.pair oriented (.const .bool b)) endpointPointCode

def direction (b : Bool) : Code InputTy .nat :=
  .comp (.pair oriented (.const .bool b)) endpointDirectionCode

def side (b : Bool) : Code InputTy .nat := .comp (direction b) sideCode

def ownerFrame : Code InputTy FrameTy :=
  .comp (.pair (.const .nat 64) (.pair (point false) (.const .bool false))) NineClusterCode.frame

def ownerState : Code InputTy SignedRunCode.StateTy :=
  .comp (.pair ownerFrame (side false)) NineClusterOwnerCode.state

def recipientAnchor : Code InputTy PointTy := .comp (point true) (scalePointCode 64)

def cut : Code InputTy .nat := .comp (side true) endCutCode

def corridor : Code InputTy CycleInputTy := .comp (.pair oriented cut) (coreCode 64 2)

/-- Same record type consumed by the complete route/receiving compiler. -/
abbrev OutputTy := Ty.pair (.pair SignedRunCode.StateTy CycleInputTy) (.pair PointTy .nat)

def code : Code InputTy OutputTy :=
  .pair (.pair ownerState corridor) (.pair recipientAnchor (side true))

end GridHardness.BipartiteRouteDataCode
