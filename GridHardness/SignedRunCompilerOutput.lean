/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCompilerSerialization

/-!
# Signed Run Compiler Output

Read the terminal signed frame and selected ideal lane.
The frame comes from the last generated rectangle, and sums extract
the coordinate fields from a singleton result.
-/

@[expose] public section

namespace GridHardness.SignedRunCompilerOutput
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode SignedRunCode
open SignedRunCardinalFormula SignedRunCompiler LatticeRouteRunsCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def sumProjection {σ : Ty} (p : Code σ .nat) : Code (.list σ) .nat :=
  .comp (.listMap p) .listSum

def boolProjection {σ : Ty} (p : Code σ .bool) : Code (.list σ) .bool :=
  .comp (.pair (sumProjection (.comp p bitNat)) (.const .nat 1)) .natEq

/-- A total list aggregate which is exactly the sole frame on singleton
inputs. No unbounded search or binary-coordinate enumeration occurs. -/
def frameOfList : Code (.list FrameTy) FrameTy :=
  let origin : Code FrameTy PointTy := .comp .snd (.comp .snd .snd)
  let x := .comp origin .fst
  let y := .comp origin .snd
  .pair (boolProjection .fst)
    (.pair (boolProjection (.comp .snd .fst))
      (.pair (boolProjection (.comp .snd (.comp .snd .fst)))
        (.pair (.pair (sumProjection (.comp x .fst)) (sumProjection (.comp x .snd)))
          (.pair (sumProjection (.comp y .fst)) (sumProjection (.comp y .snd))))))

theorem frameOfList_singleton (f : FrameTy.denote) : frameOfList.eval [f] = f := by
  rcases f with ⟨h,rx,ry,p⟩
  cases h <;> cases rx <;> cases ry <;>
    simp [frameOfList, boolProjection, sumProjection, bitNat, Code.eval]

def lastFrame : Code SignedRunCompiler.InputTy FrameTy :=
  .comp SignedRunCompiler.code
    (.comp (.pair .id (.comp (.pair .listLen (.const .nat 1)) .natSub))
      (.comp Code.listNth (.comp (.listMap .fst) frameOfList)))

theorem lastFrame_eval (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    lastFrame.eval (encodeState s,n,rs.map encodeRun,pad) =
      encodeFrame (CardinalRunChain.drawingFrom s n rs).lastFrame := by
  let xs := SignedRunCompiler.code.eval (encodeState s,n,rs.map encodeRun,pad)
  change frameOfList.eval ((Code.listNth (τ := RectangleTy)).eval (xs, xs.length - 1) |>.map Prod.fst) = _
  unfold xs
  rw [listNth_option, ← List.getLast?_eq_getElem?, code_last s n rs pad hn hb hc]
  simp only [Option.toList_some, List.map_cons, List.map_nil, segmentBox,
    GridAssembly.Rectangles.box]
  rw [frameOfList_singleton]
  exact congrArg encodeFrame (RunChain.compile_terminal s n
    (CardinalRunChain.requests s n rs)).1.symm

theorem terminal_lane_zero (s : RunState) (hs : s.lane = 0) (n : Nat)
    (rs : List RunChain.Request) : (RunChain.terminal s n rs).1.lane=0 := by
  induction rs generalizing s n with
  | nil => exact hs
  | cons r rs ih =>
    rcases r with ⟨down,m⟩
    exact ih (s.advance n down) rfl m

def lane : Code SignedRunCompiler.InputTy .bool :=
  .branch (Code.isNil (.comp .snd (.comp .snd .fst)))
    (.comp .fst (.comp .snd .snd)) (.const .bool false)

theorem lane_eval (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool) :
    lane.eval (encodeState s,n,rs.map encodeRun,pad) =
      encodeBit (RunChain.terminal s n (CardinalRunChain.requests s n rs)).1.lane := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    rcases r with ⟨d,m⟩
    have ht := terminal_lane_zero (s.advance n (s.frame.chooseTurn d)) rfl m
      (CardinalRunChain.requests (s.advance n (s.frame.chooseTurn d)) m rs)
    rw [CardinalRunChain.requests, RunChain.terminal, ht]
    simp [lane, Code.isNil, Code.eval, encodeBit]

def endpoint : Code SignedRunCompiler.InputTy (.pair FrameTy .bool) :=
  .pair lastFrame lane

/-- Exact terminal interface for subsequent collar construction. -/
theorem endpoint_eval (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    endpoint.eval (encodeState s,n,rs.map encodeRun,pad) =
      (encodeFrame (CardinalRunChain.drawingFrom s n rs).lastFrame,
        encodeBit (RunChain.terminal s n (CardinalRunChain.requests s n rs)).1.lane) := by
  exact Prod.ext (lastFrame_eval s n rs pad hn hb hc) (lane_eval s n rs pad)

end GridHardness.SignedRunCompilerOutput
