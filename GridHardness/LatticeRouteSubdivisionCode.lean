/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeInterpolationCode
public import GridHardness.LatticeRouteOrientationCode
public import GridHardness.LatticeRouteSubdivision

/-!
# Lattice Route Subdivision Code

A fixed-scale subdivision program for entire encoded routes. Each source
edge emits its half-open subdivision; exactly the final source point emits its
scaled singleton. The program agrees on all encoded lists, including empty ones.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCoreCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev AtPointTy := Ty.pair CycleInputTy (.pair PointTy .nat)

def nextPoint : Code AtPointTy CycleInputTy :=
  .comp (.pair .fst (Code.add (.comp .snd .snd) (.const .nat 1))) Code.listNth

theorem nextPoint_eval (xs : CycleInputTy.denote) (p : PointTy.denote) (i : Nat) :
    nextPoint.eval (xs,(p,i))=xs[i+1]?.toList :=
  listNth_option xs (i+1)

def sectionCode (s : Nat) : Code AtPointTy CycleInputTy :=
  .branch (Code.isNil nextPoint)
    (.comp (.comp (.comp .snd .fst) (scalePointCode s)) .listSingle)
    (.comp (.pair (.comp .snd .fst) nextPoint)
      (.comp (.listMapEnv (segmentInitCode s)) .listJoin))

def sectionResult (s : Nat) (p : PointTy.denote) : Option PointTy.denote → CycleInputTy.denote
  | none => [(scalePointCode s).eval p]
  | some q => (segmentInitCode s).eval (p,q)

theorem sectionCode_eval (s : Nat) (xs : CycleInputTy.denote) (p : PointTy.denote) (i : Nat) :
    (sectionCode s).eval (xs,(p,i))=sectionResult s p xs[i+1]? := by
  change (if decide ((nextPoint.eval (xs,(p,i))).length=0) then [(scalePointCode s).eval p]
    else ((nextPoint.eval (xs,(p,i))).map (fun q => (segmentInitCode s).eval (p,q))).flatten)=_
  rw [nextPoint_eval]
  cases h : xs[i+1]? <;> simp [sectionResult]

/-- A generic simultaneous scan of each point and its optional successor. -/
def followingScan {α β : Type*} (f : α →Option α →List β) (xs : List α) : List β :=
  xs.zipIdx.flatMap (fun q => f q.1 xs[q.2+1]?)

theorem followingScan_cons {α β : Type*} (f : α →Option α →List β) (a : α) (xs : List α) :
    followingScan f (a::xs)=f a xs.head? ++ followingScan f xs := by
  unfold followingScan
  rw [List.zipIdx_cons']
  simp only [List.flatMap_cons,List.flatMap_map,Prod.map,id_eq,
    List.getElem?_cons_succ,List.head?_eq_getElem?]

/-- `s` is a program parameter, not a binary input controlling a loop. -/
def subdivideCode (s : Nat) : Code CycleInputTy CycleInputTy :=
  .comp (.pair .id .listEnum) (.comp (.listMapEnv (sectionCode s)) .listJoin)

theorem subdivideCode_scan (s : Nat) (xs : CycleInputTy.denote) :
    (subdivideCode s).eval xs=followingScan (sectionResult s) xs := by
  change (xs.zipIdx.map (fun q => (sectionCode s).eval (xs,q))).flatten=_
  rw [← List.flatMap_def]
  apply List.flatMap_congr
  intro q _
  exact sectionCode_eval s xs q.1 q.2

/-- All interpolation points are normalized signed coordinates, and their
ordered list is exactly the established semantic subdivision. -/
theorem subdivideCode_eval (s : Nat) (xs : CycleInputTy.denote) :
    (subdivideCode s).eval xs=(LatticeSubdivision.subdivide s (xs.map decoded)).map encodePoint := by
  rw [subdivideCode_scan]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [followingScan_cons]
    cases xs with
    | nil =>
      change [(scalePointCode s).eval a]=[encodePoint (LatticeSubdivision.scale s (decoded a))]
      rw [scalePointCode_eval]
    | cons b xs =>
      change (segmentInitCode s).eval (a,b) ++ followingScan (sectionResult s) (b::xs)=
        (LatticeSubdivision.segmentInit s (decoded a) (decoded b) ++
          LatticeSubdivision.subdivide s ((b::xs).map decoded)).map encodePoint
      rw [segmentInitCode_eval,List.map_append,ih]

theorem subdivideCode_encoded (s : Nat) (xs : List (Int ×Int)) :
    (subdivideCode s).eval (xs.map encodePoint)=(LatticeSubdivision.subdivide s xs).map encodePoint := by
  rw [subdivideCode_eval,List.map_map]
  simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
  exact congrArg (fun l => (LatticeSubdivision.subdivide s l).map encodePoint) (List.map_id xs)

end GridHardness.LatticeRouteCoreCode
