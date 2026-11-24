/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCompilerOutput
public import GridHardness.TerminalCollarAttachCode

/-!
# Signed Run Receiving Code

A complete explicit cardinal-run compiler with its receiving collar.
The final strip frame and tracked lane are computed by the program, so the
caller supplies only the run data, recipient anchor, and recipient side.
-/

@[expose] public section

namespace GridHardness.SignedRunReceivingCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode SignedRunCode
open SignedTentacle.CardinalRunChain LatticeRouteRunsCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair SignedRunCompiler.InputTy (.pair PointTy .nat)

def request : Code InputTy TerminalCollarAttachCode.RequestTy :=
  let endpoint := .comp .fst SignedRunCompilerOutput.endpoint
  .pair (.comp .snd .fst) (.pair (.comp endpoint .fst)
    (.pair (.comp .snd .snd) (.comp endpoint .snd)))

def code : Code InputTy GridPointCode.InputTy :=
  .comp (.pair request (.comp .fst SignedRunCompiler.code)) TerminalCollarAttachCode.attach

private theorem encodeBit_eq (r : Fin 2) : encodeBit r=decide (r=1) := by
  fin_cases r <;> rfl

theorem request_eval (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (a : Point) (side : Fin 4) (hn : n ≤pad.length) (hb : ∀ r∈rs, r.2 ≤pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val %2≠b.val %2)) :
    request.eval ((encodeState s,n,rs.map encodeRun,pad),encodePoint a,side.val) =
      (encodePoint a,encodeFrame (drawingFrom s n rs).lastFrame,side.val,
        decide ((RunChain.terminal s n (requests s n rs)).1.lane=1)) := by
  change (encodePoint a,
    (SignedRunCompilerOutput.endpoint.eval (encodeState s,n,rs.map encodeRun,pad)).1,side.val,
    (SignedRunCompilerOutput.endpoint.eval (encodeState s,n,rs.map encodeRun,pad)).2)=_
  rw [SignedRunCompilerOutput.endpoint_eval s n rs pad hn hb hc]
  simp only [encodeBit_eq]

/-- Every rectangle of the old chain and four new receiving strips are
included, with the same phase choice as the semantic attachment construction. -/
theorem code_points (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (a : Point) (side : Fin 4) (hn : n ≤pad.length) (hb : ∀ r∈rs, r.2 ≤pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val %2≠b.val %2)) :
    GridPointCode.points (code.eval
      ((encodeState s,n,rs.map encodeRun,pad),encodePoint a,side.val)) =
      (TerminalCollarAttach.attach a (drawingFrom s n rs) side
        (RunChain.terminal s n (requests s n rs)).1.lane).points := by
  change GridPointCode.points (TerminalCollarAttachCode.attach.eval
    (request.eval ((encodeState s,n,rs.map encodeRun,pad),encodePoint a,side.val),
      SignedRunCompiler.code.eval (encodeState s,n,rs.map encodeRun,pad)))=_
  rw [request_eval s n rs pad a side hn hb hc]
  simpa only [GridAssembly.Encoding.decode_encode] using
    TerminalCollarAttachCode.attach_points (encodePoint a) (drawingFrom s n rs) side
      (RunChain.terminal s n (requests s n rs)).1.lane _
      (SignedRunCompiler.code_points s n rs pad hn hb hc)

end GridHardness.SignedRunReceivingCode
