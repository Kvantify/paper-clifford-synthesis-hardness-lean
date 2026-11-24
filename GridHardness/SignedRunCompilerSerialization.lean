/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCompiler

/-!
# Signed Run Compiler Serialization

Exact agreement between the certified run compiler and the established
rectangle serialization, with the initial and terminal records exposed for
the cluster and terminal-collar compilers.
-/

@[expose] public section

namespace GridHardness.SignedRunCompiler
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode SignedRunCode
open SignedRunCardinalFormula LatticeRouteRunsCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def placedSegmentBox (f : Frame) (r : RunChain.Segment) : RectangleTy.denote :=
  GridAssembly.Rectangles.box (f.comp r.1.frame) (r.1.length r.2+1) 2

theorem execute_serialized (f : Frame) (d : Drawing) (s : RunState) (n : Nat)
    (rs : List RunChain.Request) :
    GridAssembly.Rectangles.drawing f (RunChain.execute d s n rs) =
      GridAssembly.Rectangles.drawing f d ++
        ((RunChain.runs s n rs).tail.map (placedSegmentBox f)) := by
  induction rs generalizing d s n with
  | nil => simp [RunChain.execute, RunChain.runs]
  | cons r rs ih =>
    rcases r with ⟨down,m⟩
    rw [RunChain.execute, ih, GridAssembly.Rectangles.drawing]
    change (_ ++ [placedSegmentBox f (s.advance n down,m)]) ++
        ((RunChain.runs (s.advance n down) m rs).tail.map (placedSegmentBox f)) =
      _ ++ ((RunChain.runs (s.advance n down) m rs).map (placedSegmentBox f))
    conv_rhs => rw [RunChain.runs_self_tail]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem compile_serialized (f : Frame) (s : RunState) (n : Nat)
    (rs : List RunChain.Request) :
    GridAssembly.Rectangles.drawing f (RunChain.compile s n rs) =
      (RunChain.runs s n rs).map (placedSegmentBox f) := by
  rw [RunChain.compile, execute_serialized, GridAssembly.Rectangles.drawing]
  conv_rhs => rw [RunChain.runs_self_tail]
  rfl

theorem eastFrame_comp (f : Frame) : eastFrame.comp f = f := by
  rcases f with ⟨h,rx,ry,p⟩
  cases h <;> cases rx <;> cases ry <;>
    simp [Frame.comp, eastFrame, Frame.map, place, sign]

theorem code_serialized (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    code.eval (encodeState s,n,rs.map encodeRun,pad) =
      GridAssembly.Rectangles.drawing eastFrame (CardinalRunChain.drawingFrom s n rs) := by
  rw [code_eval_runs s n rs pad hn hb hc, CardinalRunChain.drawingFrom, compile_serialized]
  apply List.map_congr_left
  intro r _
  simp only [placedSegmentBox, segmentBox, eastFrame_comp]

theorem code_length (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    (code.eval (encodeState s,n,rs.map encodeRun,pad)).length = rs.length+1 := by
  rw [code_eval_runs s n rs pad hn hb hc, List.length_map, RunChain.runs_length,
    CardinalRunChain.requests_length]

theorem code_head (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    (code.eval (encodeState s,n,rs.map encodeRun,pad)).head? = some (segmentBox (s,n)) := by
  rw [code_eval_runs s n rs pad hn hb hc, List.head?_map, RunChain.runs_head]
  rfl

theorem code_last (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    (code.eval (encodeState s,n,rs.map encodeRun,pad)).getLast? =
      some (segmentBox (RunChain.terminal s n (CardinalRunChain.requests s n rs))) := by
  rw [code_eval_runs s n rs pad hn hb hc, List.getLast?_map, RunChain.runs_last]
  rfl

end GridHardness.SignedRunCompiler
