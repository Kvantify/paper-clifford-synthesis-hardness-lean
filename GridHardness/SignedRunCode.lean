/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyRectangles
public import GridHardness.SignedTentacleRunChain

/-!
# Signed Run Code

Certified finite-state operations for phase-corrected signed runs.
Lengths are supplied by explicit padding lists.  These operations are the
local steps of the cardinal-run compiler; no general stateful fold is
added to the polynomial builder language.
-/

@[expose] public section

namespace GridHardness.SignedRunCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev StateTy := Ty.pair FrameTy (.pair .bool .bool)
abbrev SegmentTy := Ty.pair StateTy PaddingTy
abbrev AdvanceTy := Ty.pair StateTy (.pair PaddingTy .bool)

def bit (b : Bool) : Fin 2 := if b then 1 else 0
def encodeBit (b : Fin 2) : Bool := decide (b.val = 1)

@[simp] theorem bit_encodeBit (b : Fin 2) : bit (encodeBit b) = b := by
  fin_cases b <;> rfl

@[simp] theorem encodeBit_bit (b : Bool) : encodeBit (bit b) = b := by
  cases b <;> rfl

@[simp] theorem bit_val (b : Bool) : (bit b).val = b.toNat := by
  cases b <;> rfl

def encodeState (s : RunState) : StateTy.denote :=
  (encodeFrame s.frame, encodeBit s.phase, encodeBit s.lane)

def decodeState (s : StateTy.denote) : RunState :=
  ⟨decodeFrame s.1, bit s.2.1, bit s.2.2⟩

@[simp] theorem decode_encodeState (s : RunState) : decodeState (encodeState s) = s := by
  cases s
  simp [encodeState, decodeState]

def bitNat : Code .bool .nat := .branch .id (.const .nat 1) (.const .nat 0)

@[simp] theorem bitNat_eval (b : Bool) : bitNat.eval b = b.toNat := by
  cases b <;> rfl

theorem boolNe_eval (a b : Bool) : Code.boolNe.eval (a,b) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- One explicit strip rectangle, including its phase prefix and last rung. -/
def rectangle : Code SegmentTy RectangleTy :=
  .pair (.comp .fst .fst)
    (.pair
      (Code.append .snd
        (.branch (.comp .fst (.comp .snd .fst))
          (.const PaddingTy [false,false]) (.const PaddingTy [false])))
      (.const PaddingTy [false,false]))

theorem rectangle_eval (s : RunState) (n : Nat) :
    rectangle.eval (encodeState s, List.replicate n false) =
      GridAssembly.Rectangles.box s.frame (s.length n + 1) 2 := by
  rcases s with ⟨f,h,r⟩
  fin_cases h
  · simpa [rectangle, Code.append, Code.eval, encodeState, encodeBit,
      GridAssembly.Rectangles.box, RunState.length, runLength] using
      congrArg (fun pad => (encodeFrame f, pad, List.replicate 2 false))
        (List.replicate_add n 1 false).symm
  · simpa [rectangle, Code.append, Code.eval, encodeState, encodeBit,
      GridAssembly.Rectangles.box, RunState.length, runLength,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun pad => (encodeFrame f, pad, List.replicate 2 false))
        (List.replicate_add n 2 false).symm

/-- One signed continuation. Both signs and the ideal-lane phase are computed,
and the new origin is evaluated in the previous signed frame. -/
def advance : Code AdvanceTy StateTy :=
  let f : Code AdvanceTy FrameTy := .comp .fst .fst
  let down : Code AdvanceTy .bool := .comp .snd .snd
  let phase : Code AdvanceTy .nat := .comp (.comp .fst (.comp .snd .fst)) bitNat
  let len : Code AdvanceTy .nat := .comp (.comp .snd .fst) .listLen
  let origin : Code AdvanceTy PointTy := .comp
    (.pair f (.pair (Code.add phase len) (.comp down bitNat))) GridPointCode.pointAt
  .pair
    (.pair (.comp (.comp f .fst) .boolNot)
      (.pair (.comp (.pair down (.comp f (.comp .snd (.comp .snd .fst)))) Code.boolNe)
        (.pair (.comp f (.comp .snd .fst)) origin)))
    (.pair (.comp (.pair down (.comp .fst (.comp .snd .snd))) Code.boolNe)
      (.const .bool false))

theorem advance_eval (s : RunState) (pad : PaddingTy.denote) (down : Bool) :
    advance.eval (encodeState s, pad, down) =
      encodeState (s.advance pad.length down) := by
  rcases s with ⟨⟨h,rx,ry,p⟩,phase,lane⟩
  cases h <;> cases rx <;> cases ry <;> cases down <;>
    fin_cases phase <;> fin_cases lane <;>
    simp only [advance, Code.eval, Code.add, Code.boolNe, encodeState, encodeBit,
      bitNat, GridPointCode.pointAt_eval, encodeFrame, RunState.advance, RunState.length,
      runLength, nextFrame, turnFrame, turnPhase, Frame.comp,
      decodeFrame, GridAssembly.Encoding.decode_encode]
  all_goals
    simp
    rw [GridPointCode.pointAt_eval]
    simp [decodeFrame, GridAssembly.Encoding.decode_encode]

end GridHardness.SignedRunCode
