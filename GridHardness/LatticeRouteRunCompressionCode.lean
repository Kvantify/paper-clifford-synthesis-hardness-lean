/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCodeLists
public import GridHardness.LatticeRouteRunScan

/-!
# Lattice Route Run Compression Code

A polynomial-cost program for maximal constant runs. The implementation
uses position scans, not a stateful fold or a loop over a binary run length.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRunsCode
open CliffordComplexity LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev RunTy := Ty.pair .nat .nat
abbrev RunsTy := Ty.list RunTy
abbrev AtTy := Ty.pair NatListTy RunTy

/-- The predecessor of a candidate run start, represented by a singleton. -/
def predecessor : Code AtTy NatListTy :=
  .branch (.comp (.pair (.comp .snd .snd) (.const .nat 0)) .natEq)
    (.const NatListTy [])
    (.comp (.pair .fst (.comp (.pair (.comp .snd .snd) (.const .nat 1)) .natSub)) Code.listNth)

theorem predecessor_eval (xs : List Nat) (d i : Nat) :
    predecessor.eval (xs,(d,i))=(previous none xs i).toList := by
  change (if decide (i=0) then [] else (Code.listNth (τ:=.nat)).eval (xs,i-1))=_
  by_cases hi : i=0
  · simp [hi,previous]
  · simp only [hi,decide_false,ite_false,previous]
    exact listNth_option (τ:=.nat) xs (i-1)

/-- A position starts a maximal run exactly when its predecessor differs. -/
def startsRun : Code AtTy .bool :=
  Code.isNil (.comp (.pair (.comp .snd .fst) predecessor) (Code.filterEnv .natEq))

theorem startsRun_eval (xs : List Nat) (d i : Nat) :
    startsRun.eval (xs,(d,i))=decide (previous none xs i≠some d) := by
  apply Bool.eq_iff_iff.mpr
  rw [startsRun,isNil_eval_true]
  change (Code.filterEnv Code.natEq).eval (d,predecessor.eval (xs,(d,i)))=[] ↔ _
  rw [filterEnv_eval,predecessor_eval]
  cases h : previous none xs i with
  | none => simp [Code.eval]
  | some e =>
    by_cases he : d=e
    · subst e; simp [Code.eval]
    · simp [Code.eval,he,Ne.symm he]

/-- Count precisely the equal prefix of the suffix beginning at this position. -/
def runAt : Code AtTy RunTy :=
  .pair (.comp .snd .fst)
    (.comp (.comp (.pair (.comp .snd .fst)
      (.comp (.pair .fst (.comp .snd .snd)) (dropCode .nat))) takeEqual) .listLen)

theorem runAt_eval (xs : List Nat) (d i : Nat) :
    runAt.eval (xs,(d,i))=(d,((xs.drop i).takeWhile (fun e => decide (d=e))).length) := by
  change (d,(takeEqual.eval (d,(dropCode .nat).eval (xs,i))).length)=_
  rw [dropCode_eval,takeEqual_eval]

/-- Output one record per maximal run, in the original order. -/
def compressCode : Code NatListTy RunsTy :=
  .comp (.pair .id .listEnum) (Code.filterMapEnv startsRun runAt)

theorem compressCode_eval (xs : List Nat) : compressCode.eval xs=compressNat xs := by
  rw [← scan_none,← enumScan_eq_scan none]
  change (xs.zipIdx.map (fun q => if startsRun.eval (xs,q) then [runAt.eval (xs,q)] else [])).flatten=_
  rw [← List.flatMap_def]
  unfold enumScan
  apply List.flatMap_congr
  intro q _
  rcases q with ⟨d,i⟩
  rw [startsRun_eval,runAt_eval]
  by_cases hp : previous none xs i=some d <;> simp [hp]

/-- Exact agreement with the semantic cardinal-direction representation. -/
theorem compressCode_encode (ds : List (Fin 4)) :
    compressCode.eval (ds.map Fin.val)=(LatticeRouteRuns.compressDirections ds).map encodeRun := by
  rw [compressCode_eval,compressNat_encode]

end GridHardness.LatticeRouteRunsCode
