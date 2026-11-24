/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunReceivingCode
public import GridHardness.SatOwnerStripCode
public import GridHardness.SatCompleteTentacles

/-!
# SAT Complete Tentacle Code

An executable compiler for complete SAT tentacles. It computes maximal
runs, derives padding from the route, emits signed strips, extracts the terminal
frame and lane, selects the receiving phase, and appends four collar strips.
Its input consists of route and placement data. `SatDirectedRecordsCode` and
`SatBipartiteRecordsCode` generate that data from SAT syntax.
-/

@[expose] public section

namespace GridHardness.SatCompleteTentacleCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode
set_option autoImplicit false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair LatticeRouteStripCode.InputTy (.pair PointTy .nat)

def code : Code InputTy GridPointCode.InputTy :=
  .comp (.pair (.comp .fst LatticeRouteStripCode.prepare) .snd) SignedRunReceivingCode.code

noncomputable def input (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    InputTy.denote :=
  (SatOwnerStripCode.input x hw e,
    encodePoint (SatCompleteTentacles.anchor x hw e),(SatCompleteTentacles.side x hw e).val)

noncomputable def rectangles (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : SatDockCorridors.Edge x) : GridPointCode.InputTy.denote := code.eval (input x hw e)

/-- Exact equality with the complete, geometrically verified SAT tentacle,
including its two endpoint interfaces; no additional geometric premise remains. -/
theorem points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : SatDockCorridors.Edge x) :
    GridPointCode.points (rectangles x hw e)=(SatCompleteTentacles.drawing x hw e).points := by
  change GridPointCode.points (SignedRunReceivingCode.code.eval
    (LatticeRouteStripCode.prepare.eval (SatOwnerStripCode.input x hw e),
      encodePoint (SatCompleteTentacles.anchor x hw e),(SatCompleteTentacles.side x hw e).val))=_
  rw [SatOwnerStripCode.prepared]
  obtain ⟨hn,hb⟩ := SatOwnerStripCode.reservoir_bounds x hw e
  exact SignedRunReceivingCode.code_points (SatOwnerTentacles.state x hw e)
    (SatOwnerTentacles.firstRun x hw e).2 (SatOwnerTentacles.remaining x hw e) _
    (SatCompleteTentacles.anchor x hw e) (SatCompleteTentacles.side x hw e)
    hn hb (SatOwnerTentacles.directions x hw e)

end GridHardness.SatCompleteTentacleCode
