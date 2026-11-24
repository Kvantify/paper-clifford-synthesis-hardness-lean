/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteStripCode
public import GridHardness.SatOwnerTentacles

/-!
# SAT Owner Strip Code

The executable route-to-strip compiler realizes each actual owner tentacle.
The source-dependent route and initial state remain semantic inputs here; once
these inputs are supplied, compression and complete strip serialization are
performed by the proved polynomial program.
-/

@[expose] public section

namespace GridHardness.SatOwnerStripCode
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

abbrev Edge := SatDockCorridors.Edge

noncomputable def input (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteStripCode.InputTy.denote :=
  (SignedRunCode.encodeState (SatOwnerTentacles.state x hw e),
    (SatDockCorridors.route x hw e).map encodePoint)

noncomputable def rectangles (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    GridPointCode.InputTy.denote := LatticeRouteStripCode.code.eval (input x hw e)

/-- The exact prepared signed-compiler input, including its route-derived
unary padding reservoir. -/
theorem prepared (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteStripCode.prepare.eval (input x hw e)=
      (SignedRunCode.encodeState (SatOwnerTentacles.state x hw e),
        (SatOwnerTentacles.firstRun x hw e).2,
        (SatOwnerTentacles.remaining x hw e).map LatticeRouteRunsCode.encodeRun,
        List.replicate (SatDockCorridors.route x hw e).length false) := by
  have hd : ((SatDockCorridors.route x hw e).map encodePoint).map decoded=
      SatDockCorridors.route x hw e := by
    rw [List.map_map]
    simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
    exact List.map_id _
  have hr : LatticeRouteRuns.compress (((SatDockCorridors.route x hw e).map encodePoint).map decoded)=
      ((SatOwnerTentacles.state x hw e).frame.axisDirection,(SatOwnerTentacles.firstRun x hw e).2)::
        SatOwnerTentacles.remaining x hw e := by
    rw [hd]
    exact SatOwnerTentacles.runs_decompose x hw e
  simpa only [input,List.length_map] using LatticeRouteStripCode.prepare_eval
    (SatOwnerTentacles.state x hw e) ((SatDockCorridors.route x hw e).map encodePoint)
    (SatOwnerTentacles.firstRun x hw e).2 (SatOwnerTentacles.remaining x hw e) hr

/-- The actual route length bounds every run, including the first one. -/
theorem run_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (SatOwnerTentacles.firstRun x hw e).2≤(SatDockCorridors.route x hw e).length ∧
      ∀ r∈SatOwnerTentacles.remaining x hw e,r.2≤(SatDockCorridors.route x hw e).length := by
  have hd : ((SatDockCorridors.route x hw e).map encodePoint).map decoded=
      SatDockCorridors.route x hw e := by
    rw [List.map_map]
    simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
    exact List.map_id _
  have hr : LatticeRouteRuns.compress (((SatDockCorridors.route x hw e).map encodePoint).map decoded)=
      ((SatOwnerTentacles.state x hw e).frame.axisDirection,(SatOwnerTentacles.firstRun x hw e).2)::
        SatOwnerTentacles.remaining x hw e := by
    rw [hd]
    exact SatOwnerTentacles.runs_decompose x hw e
  simpa only [List.length_map] using LatticeRouteStripCode.reservoir_bounds
    ((SatDockCorridors.route x hw e).map encodePoint) (SatOwnerTentacles.state x hw e).frame.axisDirection
    (SatOwnerTentacles.firstRun x hw e).2 (SatOwnerTentacles.remaining x hw e) hr

theorem reservoir_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (SatOwnerTentacles.firstRun x hw e).2≤
        (List.replicate (SatDockCorridors.route x hw e).length false).length ∧
      ∀ r∈SatOwnerTentacles.remaining x hw e,r.2≤
        (List.replicate (SatDockCorridors.route x hw e).length false).length := by
  simpa only [List.length_replicate] using run_bounds x hw e

/-- Every actual uncollared owner tentacle is realized by an executable
route-to-rectangle program, with no additional geometry hypothesis. -/
theorem points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    GridPointCode.points (rectangles x hw e)=(SatOwnerTentacles.drawing x hw e).points := by
  exact LatticeRouteStripCode.code_points_encoded
    (SatOwnerTentacles.state x hw e) (SatDockCorridors.route x hw e)
    (SatOwnerTentacles.firstRun x hw e).2 (SatOwnerTentacles.remaining x hw e)
    (SatOwnerTentacles.runs_decompose x hw e)
    (SatDockCorridors.route_certificate x hw e).2.2.1
    (SatDockCorridors.route_certificate x hw e).2.2.2.1

end GridHardness.SatOwnerStripCode
