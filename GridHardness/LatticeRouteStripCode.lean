/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteStripPreparation
public import GridHardness.SignedRunCompiler

/-!
# Lattice Route Strip Code

A connected polynomial compiler from an encoded point route and initial
signed state to strip rectangles. Maximal runs and their unary padding are
computed from the input route. Correctness is tied to the existing drawing
constructor; simple unit routes supply perpendicularity automatically.
-/

@[expose] public section

namespace GridHardness.LatticeRouteStripCode
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open GridProblems GridProblems.GridCode GridPointCode LatticeRouteRunsCode SignedRunCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def code : Code InputTy GridPointCode.InputTy := .comp prepare SignedRunCompiler.code

/-- Exact rectangle-list evaluation, with all run extraction and padding
performed by the program. -/
theorem code_eval_runs (s : RunState) (xs : CycleInputTy.denote)
    (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hr : LatticeRouteRuns.compress (xs.map decoded) =(s.frame.axisDirection,n)::rs)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2)) :
    code.eval (encodeState s,xs)=
      (RunChain.runs s n (CardinalRunChain.requests s n rs)).map SignedRunCompiler.segmentBox := by
  change SignedRunCompiler.code.eval (prepare.eval (encodeState s,xs))=_
  rw [prepare_eval s xs n rs hr]
  have hb := reservoir_bounds xs s.frame.axisDirection n rs hr
  exact SignedRunCompiler.code_eval_runs s n rs _
    (by simpa only [List.length_replicate] using hb.1)
    (by simpa only [List.length_replicate] using hb.2) hc

/-- The actual rectangle union is exactly the existing signed cardinal drawing. -/
theorem code_points (s : RunState) (xs : CycleInputTy.denote)
    (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hr : LatticeRouteRuns.compress (xs.map decoded) =(s.frame.axisDirection,n)::rs)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2)) :
    GridPointCode.points (code.eval (encodeState s,xs))=(CardinalRunChain.drawingFrom s n rs).points := by
  change GridPointCode.points (SignedRunCompiler.code.eval (prepare.eval (encodeState s,xs)))=_
  rw [prepare_eval s xs n rs hr]
  have hb := reservoir_bounds xs s.frame.axisDirection n rs hr
  exact SignedRunCompiler.code_points s n rs _
    (by simpa only [List.length_replicate] using hb.1)
    (by simpa only [List.length_replicate] using hb.2) hc

/-- A simple unit route needs no separate turn certificate. -/
theorem code_points_route (s : RunState) (xs : CycleInputTy.denote)
    (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hr : LatticeRouteRuns.compress (xs.map decoded) =(s.frame.axisDirection,n)::rs)
    (hn : (xs.map decoded).Nodup)
    (hu : (xs.map decoded).IsChain LatticeSubdivision.UnitStep) :
    GridPointCode.points (code.eval (encodeState s,xs))=(CardinalRunChain.drawingFrom s n rs).points :=
  code_points s xs n rs hr (compressed_perpendicular xs s.frame.axisDirection n rs hr hn hu)

theorem compress_nonempty (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    LatticeRouteRuns.compress (xs.map decoded)≠[] := by
  intro he
  have hs := LatticeRouteRuns.run_step_count (xs.map decoded)
  rw [he] at hs
  simp only [List.map_nil,List.sum_nil,List.length_map] at hs
  exact (Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1<2) hl))) hs.symm

/-- These are computed by compression, rather than supplied as a decomposition. -/
def firstRun (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) : LatticeRouteRuns.Run :=
  (LatticeRouteRuns.compress (xs.map decoded)).head (compress_nonempty xs hl)

def tailRuns (xs : CycleInputTy.denote) : List LatticeRouteRuns.Run :=
  (LatticeRouteRuns.compress (xs.map decoded)).tail

theorem runs_decompose (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    LatticeRouteRuns.compress (xs.map decoded)=
      ((firstRun xs hl).1,(firstRun xs hl).2)::tailRuns xs :=
  (List.cons_head_tail (compress_nonempty xs hl)).symm

/-- The sole directional agreement is with the prescribed initial frame;
the run list, run lengths, padding, and all later turns are computed. -/
theorem code_points_computed (s : RunState) (xs : CycleInputTy.denote)
    (hl : 2 ≤ xs.length) (hs : (firstRun xs hl).1 = s.frame.axisDirection)
    (hn : (xs.map decoded).Nodup)
    (hu : (xs.map decoded).IsChain LatticeSubdivision.UnitStep) :
    GridPointCode.points (code.eval (encodeState s,xs))=
      (CardinalRunChain.drawingFrom s (firstRun xs hl).2 (tailRuns xs)).points := by
  apply code_points_route s xs (firstRun xs hl).2 (tailRuns xs) ?_ hn hu
  rw [← hs]
  exact runs_decompose xs hl

theorem code_points_encoded (s : RunState) (xs : List (Int × Int))
    (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hr : LatticeRouteRuns.compress xs =(s.frame.axisDirection,n)::rs)
    (hn : xs.Nodup) (hu : xs.IsChain LatticeSubdivision.UnitStep) :
    GridPointCode.points (code.eval (encodeState s,xs.map encodePoint))=
      (CardinalRunChain.drawingFrom s n rs).points := by
  have he : (xs.map encodePoint).map decoded=xs := by
    rw [List.map_map]
    simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
    exact List.map_id xs
  apply code_points_route s (xs.map encodePoint) n rs
  · simpa only [he] using hr
  · simpa only [he] using hn
  · simpa only [he] using hu

end GridHardness.LatticeRouteStripCode
