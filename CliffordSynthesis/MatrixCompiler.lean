/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Problems
public import CliffordComplexity.Reduction

/-!
# Matrix Compiler

Dense Boolean output, compiled by the polynomial builder language.  The
two matrices are the X block and the inverse-transpose Z block; the other
two blocks are explicitly zero in `decode`.
-/

@[expose] public section

namespace CliffordSynthesis.MatrixCompiler

open CliffordComplexity

variable {α : Type*}

abbrev TemplateTy := Ty.pair RowTy MatrixTy

def zeroes (l : List α) : List Bool := l.map (fun _ => false)
def ones (l : List α) : List Bool := l.map (fun _ => true)
def basis (l : List α) (i : Nat) : List Bool := (List.range l.length).map (fun j => decide (i = j))

def zeroCode (τ : Ty) : Code (.list τ) RowTy := .listMap (.const .bool false)
def oneCode (τ : Ty) : Code (.list τ) RowTy := .listMap (.const .bool true)
def basisCode (τ : Ty) : Code (.pair (.list τ) .nat) RowTy :=
  .comp (.pair .snd (.comp .fst Code.indices)) (.listMapEnv .natEq)
def bitCode : Code (.pair RowTy .nat) .bool :=
  .comp Code.listNth (.comp (.listFilter .id)
    (.comp .listLen (.comp (.pair (.const .nat 1) .id) .natLe)))

@[simp] theorem basisCode_eval (τ : Ty) (l : List τ.denote) (i : Nat) :
    (basisCode τ).eval (l, i) = basis l i := by
  simp [basisCode, Code.eval, CliffordComplexity.indices_eval, basis]

@[simp] theorem bitCode_eval (l : List Bool) (i : Nat) :
    bitCode.eval (l, i) = readBit l i := by
  by_cases h : i < l.length
  · change decide (1 ≤ (((Code.listNth (τ := .bool)).eval (l, i)).filter id).length) = _
    rw [listNth_eval (τ := .bool) h]
    simp only [readBit, List.getElem?_eq_getElem h, Option.getD_some]
    cases l[i] <;> rfl
  · change decide (1 ≤ (((Code.listNth (τ := .bool)).eval (l, i)).filter id).length) = _
    rw [listNth_eval_of_le (τ := .bool) (by omega)]
    simp only [readBit]
    rw [List.getElem?_eq_none (show l.length ≤ i by omega)]
    rfl

def rowA (t : List Bool) (X : List (List Bool)) : List (List Bool) :=
  ((List.range t.length).map fun j => basis t j ++ [false] ++ zeroes X) ++
    [t ++ [true] ++ zeroes X] ++
    (X.zipIdx.map fun q => q.1 ++ [true] ++ basis X q.2)

def rowB (t : List Bool) (X : List (List Bool)) : List (List Bool) :=
  ((List.range t.length).map fun j => basis t j ++ [readBit t j] ++
    X.map (fun x => readBit x j ^^ readBit t j)) ++
    [zeroes t ++ [true] ++ ones X] ++
    (List.range X.length).map (fun a => zeroes t ++ [false] ++ basis X a)

def coordinateA : Code (.pair TemplateTy .nat) RowTy :=
  Code.append (.comp (.pair (.comp .fst .fst) .snd) (basisCode .bool))
    (Code.cons (.const .bool false) (.comp (.comp .fst .snd) (zeroCode RowTy)))

def pathA : Code TemplateTy RowTy :=
  Code.append .fst (Code.cons (.const .bool true) (.comp .snd (zeroCode RowTy)))

def recorderA : Code (.pair MatrixTy (.pair RowTy .nat)) RowTy :=
  Code.append (.comp .snd .fst)
    (Code.cons (.const .bool true) (.comp (.pair .fst (.comp .snd .snd)) (basisCode RowTy)))

def aCode : Code TemplateTy MatrixTy :=
  Code.append
    (.comp (.pair .id (.comp .fst Code.indices)) (.listMapEnv coordinateA))
    (Code.cons pathA (.comp (.pair .snd (.comp .snd .listEnum)) (.listMapEnv recorderA)))

def inverseEntry : Code (.pair (.pair RowTy .nat) RowTy) .bool :=
  .comp (.pair (.comp (.pair .snd (.comp .fst .snd)) bitCode) (.comp .fst bitCode)) Code.boolNe

def coordinateB : Code (.pair TemplateTy .nat) RowTy :=
  Code.append (.comp (.pair (.comp .fst .fst) .snd) (basisCode .bool))
    (Code.cons (.comp (.pair (.comp .fst .fst) .snd) bitCode)
      (.comp (.pair (.pair (.comp .fst .fst) .snd) (.comp .fst .snd))
        (.listMapEnv inverseEntry)))

def pathB : Code TemplateTy RowTy :=
  Code.append (.comp .fst (zeroCode .bool))
    (Code.cons (.const .bool true) (.comp .snd (oneCode RowTy)))

def recorderB : Code (.pair TemplateTy .nat) RowTy :=
  Code.append (.comp (.comp .fst .fst) (zeroCode .bool))
    (Code.cons (.const .bool false)
      (.comp (.pair (.comp .fst .snd) .snd) (basisCode RowTy)))

def bCode : Code TemplateTy MatrixTy :=
  Code.append
    (.comp (.pair .id (.comp .fst Code.indices)) (.listMapEnv coordinateB))
    (Code.cons pathB
      (.comp (.pair .id (.comp .snd Code.indices)) (.listMapEnv recorderB)))

theorem boolNe_eq_xor (a b : Bool) : Code.boolNe.eval (a, b) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem aCode_eval (t : List Bool) (X : List (List Bool)) :
    aCode.eval (t, X) = rowA t X := by
  simp only [aCode, Code.append, Code.cons, Code.eval, indices_eval]
  simp only [coordinateA, pathA, recorderA, Code.append, Code.cons, Code.eval, zeroCode]
  simp only [basisCode_eval .bool t, basisCode_eval RowTy X]
  simp only [rowA, zeroes, List.append_assoc, List.singleton_append]

@[simp] theorem bCode_eval (t : List Bool) (X : List (List Bool)) :
    bCode.eval (t, X) = rowB t X := by
  simp only [bCode, Code.append, Code.cons, Code.eval, indices_eval]
  simp only [coordinateB, pathB, recorderB, inverseEntry, Code.append, Code.cons,
    Code.eval, zeroCode, oneCode]
  simp only [basisCode_eval .bool t, basisCode_eval RowTy X]
  have hb : bitCode.eval = (fun p => readBit p.1 p.2) := by
    funext p
    exact bitCode_eval p.1 p.2
  have hx : Code.boolNe.eval = (fun p => p.1 ^^ p.2) := by
    funext p
    exact boolNe_eq_xor p.1 p.2
  simp only [hb, hx]
  simp only [rowB, zeroes, ones, List.append_assoc, List.singleton_append]

def compile : Code (.pair TemplateTy .nat) OutputTy :=
  .pair (.comp .fst aCode) (.pair (.comp .fst bCode) .snd)

@[simp] theorem compile_eval (t : List Bool) (X : List (List Bool)) (k : Nat) :
    compile.eval ((t, X), k) = (rowA t X, (rowB t X, k)) := by
  change (aCode.eval (t, X), (bCode.eval (t, X), k)) = _
  rw [aCode_eval, bCode_eval]

end CliffordSynthesis.MatrixCompiler
