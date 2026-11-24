/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.Reduction
public import Mathlib.Tactic

/-!
# Encoding

Binary signed coordinates and source-only polynomial builder programs.
-/

@[expose] public section

namespace GridProblems.GridCode
open CliffordComplexity

abbrev SignedTy := Ty.pair .nat .nat
abbrev PointTy := Ty.pair SignedTy SignedTy
abbrev InputTy := Ty.pair (Ty.list PointTy) .nat
def integer (p : Nat × Nat) : Int := (p.1 : Int) - p.2

def encodeInt (z : Int) : Nat × Nat := (z.toNat, (-z).toNat)

def encodePoint (p : Int × Int) : PointTy.denote := (encodeInt p.1, encodeInt p.2)

@[simp] theorem integer_encodeInt (z : Int) : integer (encodeInt z) = z := by
  unfold integer encodeInt
  omega

def tailCode (τ : Ty) : Code (.list τ) (.list τ) :=
  .comp .listEnum (.comp (.listFilter (.comp (.pair (.const .nat 0) .snd) Code.natLt))
    (.listMap .fst))

theorem tailCode_eval (τ : Ty) (l : List τ.denote) : (tailCode τ).eval l = l.tail := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [tailCode, Code.eval, List.zipIdx_cons, List.filter_cons]
    have h : ((l.zipIdx 1).filter fun q => Code.natLt.eval (0, q.2)) = l.zipIdx 1 := by
      apply List.filter_eq_self.mpr
      intro q hq
      rw [natLt_eval, decide_eq_true_eq]
      have := List.le_snd_of_mem_zipIdx hq
      omega
    rw [h]
    exact List.zipIdx_map_fst 1 l

def lookupNat (τ : Ty) (component : Code τ .nat) : Code (.pair (.list τ) .nat) .nat :=
  .comp Code.listNth (.comp (.listMap component) .listSum)

theorem lookupNat_eval (τ : Ty) (component : Code τ .nat) (l : List τ.denote)
    (i : Nat) (h : i < l.length) : (lookupNat τ component).eval (l, i) = component.eval l[i] := by
  change ((Code.listNth.eval (l, i)).map component.eval).sum = _
  rw [listNth_eval (τ := τ) h]
  simp

def start : Code InputTy PointTy :=
  let first := Code.pair Code.fst (Code.const .nat 0)
  .pair
    (.pair (.comp first (lookupNat PointTy (.comp .fst .fst)))
      (.comp first (lookupNat PointTy (.comp .fst .snd))))
    (.pair (.comp first (lookupNat PointTy (.comp .snd .fst)))
      (.comp first (lookupNat PointTy (.comp .snd .snd))))

def count : Code InputTy .nat :=
  .comp (.pair (.comp .fst .listLen) (.const .nat 1)) .natSub

def allCode : Code (.list .bool) .bool :=
  Code.isNil (.listFilter .boolNot)

variable {m : Nat}

def decoded (p : PointTy.denote) : Int × Int := (integer p.1, integer p.2)
def input (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) : InputTy.denote :=
  (List.ofFn p, last.val)

@[simp] theorem start_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    start.eval (input p last) = p 0 := by
  have h : 0 < (List.ofFn p).length := by simp
  simp only [start, Code.eval, input]
  simp only [lookupNat_eval PointTy _ _ 0 h, List.getElem_ofFn, Code.eval]
  rfl

@[simp] theorem count_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    count.eval (input p last) = m := by
  simp [count, Code.eval, input]

theorem allCode_eval (l : List Bool) : allCode.eval l = true ↔ ∀ b ∈ l, b = true := by
  rw [allCode, isNil_eval_true]
  change (l.filter Bool.not) = [] ↔ _
  simp

end GridProblems.GridCode
