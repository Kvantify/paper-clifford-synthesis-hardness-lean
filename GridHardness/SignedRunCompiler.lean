/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCardinalCode

/-!
# Signed Run Compiler

A polynomial builder program for a complete phase-corrected cardinal
strip chain. All run positions and unary output lengths are drawn from
explicit input lists. Correctness requires perpendicular successive cardinal
directions and a reservoir at least as long as each requested run.
-/

@[expose] public section

namespace GridHardness.SignedRunCompiler
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode SignedRunCode
open SignedRunCardinalFormula SignedRunCardinalCode LatticeRouteRunsCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev EnvTy := Ty.pair PointTy (.pair (.list .bool) (.pair SignedRunCardinalCode.RunsTy PaddingTy))
abbrev IndexedTy := Ty.pair SignedRunCardinalCode.RunTy .nat
abbrev InputTy := Ty.pair StateTy (.pair .nat (.pair SignedRunCardinalCode.RunsTy PaddingTy))

def env (p : Point) (older previous : Bool) (rs : List Run) (pad : List Bool) : EnvTy.denote :=
  (encodePoint p, signHistory older previous rs, rs.map encodeRun, pad)

def segmentBox (r : RunChain.Segment) : RectangleTy.denote :=
  GridAssembly.Rectangles.box r.1.frame (r.1.length r.2+1) 2

/-- Evaluate one indexed run by prefix sums and two sign-history lookups. -/
def recipe : Code (.pair EnvTy IndexedTy) RectangleTy :=
  let i : Code (.pair EnvTy IndexedTy) .nat := .comp .snd .snd
  let r : Code (.pair EnvTy IndexedTy) SignedRunCardinalCode.RunTy := .comp .snd .fst
  let hist : Code (.pair EnvTy IndexedTy) (.list .bool) := .comp .fst (.comp .snd .fst)
  let runs : Code (.pair EnvTy IndexedTy) SignedRunCardinalCode.RunsTy :=
    .comp .fst (.comp .snd (.comp .snd .fst))
  let pad : Code (.pair EnvTy IndexedTy) PaddingTy :=
    .comp .fst (.comp .snd (.comp .snd .snd))
  let p := .comp (.pair (.comp .fst .fst)
    (.comp (.pair runs i) (takeCode SignedRunCardinalCode.RunTy))) translateCode
  let previous := .comp (.pair hist (Code.add i (.const .nat 1))) boolAt
  let older := .comp (.pair hist i) boolAt
  let state := .comp (.pair p (.pair (.comp r .fst) (.pair previous older))) regularCode
  .comp (.pair state (.comp (.pair pad (.comp r .snd)) padding)) SignedRunCode.rectangle

theorem recipe_eval (p : Point) (older previous : Bool) (rs : List Run)
    (pad : List Bool) (d : Fin 4) (n i : Nat) (hn : n ≤ pad.length) :
    recipe.eval (env p older previous rs pad, (encodeRun (d,n),i)) =
      segmentBox (regular (translate p (rs.take i)) d
        ((signHistory older previous rs)[i+1]?.getD false)
        ((signHistory older previous rs)[i]?.getD false),n) := by
  simp only [recipe, Code.eval, Code.add, env, encodeRun]
  rw [takeCode_eval, ← List.map_take, translateCode_eval, boolAt_eval, boolAt_eval,
    regularCode_eval, padding_eval pad n hn, SignedRunCode.rectangle_eval]
  rfl

def tailCode : Code EnvTy GridPointCode.InputTy :=
  .comp (.pair .id (.comp (.comp .snd (.comp .snd .fst)) .listEnum)) (.listMapEnv recipe)

theorem tailCode_eval (p : Point) (older previous : Bool) (rs : List Run)
    (pad : List Bool) (hn : ∀ r ∈rs, r.2 ≤ pad.length) :
    tailCode.eval (env p older previous rs pad) =
      (indexedRuns p older previous rs).map segmentBox := by
  simp only [tailCode, Code.eval, env, List.zipIdx_map, List.map_map, indexedRuns]
  apply List.map_congr_left
  intro r hr
  have hm : r.1 ∈ rs := List.fst_mem_of_mem_zipIdx hr
  rcases r with ⟨⟨d,n⟩,i⟩
  exact recipe_eval p older previous rs pad d n i (hn _ hm)

/-- The ideal point at any requested nonnegative run parameter. -/
def pointCode : Code (.pair StateTy .nat) PointTy :=
  .comp (.pair (.comp .fst .fst)
    (.pair (Code.add (.comp (.comp .fst (.comp .snd .fst)) bitNat) .snd)
      (.comp (.comp .fst (.comp .snd .snd)) bitNat))) GridPointCode.pointAt

theorem pointCode_eval (s : RunState) (n : Nat) :
    pointCode.eval (encodeState s,n) = encodePoint (s.point n) := by
  simp only [pointCode, Code.eval, Code.add, encodeState]
  rw [bitNat_eval, bitNat_eval, GridPointCode.pointAt_eval, decode_encodeFrame]
  have hp : (encodeBit s.phase).toNat=s.phase.val := by
    have h := bit_val (encodeBit s.phase)
    simpa using h.symm
  have hr : (encodeBit s.lane).toNat=s.lane.val := by
    have h := bit_val (encodeBit s.lane)
    simpa using h.symm
  simp only [hp, hr, RunState.point, runPoint, Nat.cast_add]

/-- Build the reusable environment from the arbitrary initial state. -/
def environment : Code InputTy EnvTy :=
  let s : Code InputTy StateTy := .fst
  let f : Code InputTy FrameTy := .comp s .fst
  let runs : Code InputTy SignedRunCardinalCode.RunsTy := .comp .snd (.comp .snd .fst)
  let older : Code InputTy .bool := .comp (.pair
    (.comp f (.comp .snd (.comp .snd .fst))) (.comp s (.comp .snd .snd))) GridFrameCode.xor
  let previous := .comp f (.comp .snd .fst)
  let history := Code.cons older (Code.cons previous
    (.comp runs (.listMap (.comp .fst negativeCode))))
  .pair (.comp (.pair s (.comp .snd .fst)) pointCode)
    (.pair history (.pair runs (.comp .snd (.comp .snd .snd))))

theorem environment_eval (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool) :
    environment.eval (encodeState s,n,rs.map encodeRun,pad) =
      env (s.point n) (s.frame.reverseY ^^ encodeBit s.lane) s.frame.reverseX rs pad := by
  simp only [environment, Code.eval, Code.cons, Code.append]
  rw [pointCode_eval]
  simp only [encodeState, encodeFrame]
  rw [GridFrameCode.xor_eval]
  simp only [env, signHistory, List.map_map, List.singleton_append]
  rfl

/-- The full compiler materializes the initial strip and all indexed runs. -/
def code : Code InputTy GridPointCode.InputTy :=
  Code.cons
    (.comp (.pair .fst (.comp (.pair (.comp .snd (.comp .snd .snd))
      (.comp .snd .fst)) padding)) SignedRunCode.rectangle)
    (.comp environment tailCode)

/-- Exact serialization of the generated state sequence, not merely a
coordinate containment or a size estimate. -/
theorem code_eval_runs (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    code.eval (encodeState s,n,rs.map encodeRun,pad) =
      (RunChain.runs s n (CardinalRunChain.requests s n rs)).map segmentBox := by
  simp only [code, Code.cons, Code.eval]
  rw [padding_eval pad n hn, SignedRunCode.rectangle_eval, environment_eval,
    tailCode_eval _ _ _ _ _ hb]
  rw [← initial_indexedRuns s n rs hc]
  rfl

/-- The concrete rectangle compiler agrees exactly with the established
cardinal drawing constructor. Clearance is not needed for this identity. -/
theorem code_points (s : RunState) (n : Nat) (rs : List Run) (pad : List Bool)
    (hn : n ≤ pad.length) (hb : ∀ r ∈rs, r.2 ≤ pad.length)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2≠b.val % 2)) :
    GridPointCode.points (code.eval (encodeState s,n,rs.map encodeRun,pad)) =
      (CardinalRunChain.drawingFrom s n rs).points := by
  rw [code_eval_runs s n rs pad hn hb hc]
  ext p
  rw [CardinalRunChain.drawingFrom, RunChain.compile_mem]
  simp only [GridPointCode.points, Finset.mem_biUnion, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨r,⟨a,ha,rfl⟩,hp⟩
    exact ⟨a,ha,by simpa only [segmentBox, GridAssembly.Rectangles.box_strip,
      RunChain.segmentStrip] using hp⟩
  · rintro ⟨a,ha,hp⟩
    exact ⟨segmentBox a,⟨a,ha,rfl⟩,by simpa only [segmentBox,
      GridAssembly.Rectangles.box_strip,RunChain.segmentStrip] using hp⟩

end GridHardness.SignedRunCompiler
