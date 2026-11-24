/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
public import Mathlib.Data.List.OfFn

/-!
# Program

Compositional polynomial-time programs for the instance encodings.
-/

@[expose] public section

namespace CliffordComplexity

open Turing.MultiTapeTM
set_option autoImplicit false

/-- Types with compositional encodings as framed binary words. -/
inductive Ty where
  | nat
  | bool
  | pair (left right : Ty)
  | list (element : Ty)

/-- The Lean type represented by an encoding descriptor. -/
@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .pair s t => s.denote × t.denote
  | .list s => List s.denote

/-- Encode each value using Frontier’s binary natural, list, and pair encodings. -/
def encodeTy : (t : Ty) → t.denote ↪ List Bool
  | .nat => encNat
  | .bool => encBool
  | .pair s t => encPair (encodeTy s) (encodeTy t)
  | .list s => encList (encodeTy s)

/-- Programs over framed binary encodings. Operations process the explicit
list structure, including when a list length controls an exponent. -/
inductive Code : Ty → Ty → Type where
  | id {s} : Code s s
  | comp {s t u} : Code s t → Code t u → Code s u
  | fst {s t} : Code (.pair s t) s
  | snd {s t} : Code (.pair s t) t
  | pair {s t u} : Code s t → Code s u → Code s (.pair t u)
  | const {s} (t : Ty) : t.denote → Code s t
  | branch {s t} : Code s .bool → Code s t → Code s t → Code s t
  | natAdd : Code (.pair .nat .nat) .nat
  | natSub : Code (.pair .nat .nat) .nat
  | natMul : Code (.pair .nat .nat) .nat
  | natLe : Code (.pair .nat .nat) .bool
  | listLen {s} : Code (.list s) .nat
  | listMap {s t} : Code s t → Code (.list s) (.list t)
  | boolNot : Code .bool .bool
  | boolAnd : Code (.pair .bool .bool) .bool
  | boolOr : Code (.pair .bool .bool) .bool
  | natEq : Code (.pair .nat .nat) .bool
  | listSingle {s} : Code s (.list s)
  | listAppend {s} : Code (.pair (.list s) (.list s)) (.list s)
  | listJoin {s} : Code (.list (.list s)) (.list s)
  | listFilter {s} : Code s .bool → Code (.list s) (.list s)
  | listMapEnv {e s t} : Code (.pair e s) t → Code (.pair e (.list s)) (.list t)
  | listEnum {s} : Code (.list s) (.list (.pair s .nat))
  | listSum : Code (.list .nat) .nat
  | natPowLen {s} : Code (.pair .nat (.list s)) .nat
  | listNth {τ} : Code (.pair (.list τ) .nat) (.list τ)
  | boolNe : Code (.pair .bool .bool) .bool
  | ofPolyTime {s t} (f : s.denote → t.denote)
      (hf : ComputableInPolyTime f (encodeTy s) (encodeTy t)) : Code s t

namespace Code

variable {s t : Ty}

/-- Evaluate a program on a value of its source type. -/
def eval {s t : Ty} : Code s t → s.denote → t.denote
  | .id, x => x
  | .comp f g, x => g.eval (f.eval x)
  | .fst, x => x.1
  | .snd, x => x.2
  | .pair f g, x => (f.eval x, g.eval x)
  | .const _ a, _ => a
  | .branch p f g, x => if p.eval x then f.eval x else g.eval x
  | .natAdd, x => x.1 + x.2
  | .natSub, x => x.1 - x.2
  | .natMul, x => x.1 * x.2
  | .natLe, x => decide (x.1 ≤ x.2)
  | .listLen, xs => xs.length
  | .listMap f, xs => xs.map f.eval
  | .boolNot, x => !x
  | .boolAnd, x => x.1 && x.2
  | .boolOr, x => x.1 || x.2
  | .natEq, x => decide (x.1 = x.2)
  | .listSingle, x => [x]
  | .listAppend, x => x.1 ++ x.2
  | .listJoin, xs => xs.flatten
  | .listFilter p, xs => xs.filter p.eval
  | .listMapEnv f, x => x.2.map (fun a => f.eval (x.1, a))
  | .listEnum, xs => xs.zipIdx
  | .listSum, xs => xs.sum
  | .natPowLen, x => x.1 ^ x.2.length
  | .listNth, x => (x.1.map fun a => [a]).getD x.2 []
  | .boolNe, x => x.1 ^^ x.2
  | .ofPolyTime f _, x => f x

/-- Evaluation is polynomial-time on the framed input and output encodings. -/
theorem polyTime (c : Code s t) :
    ComputableInPolyTime c.eval (encodeTy s) (encodeTy t) := by
  induction c with
  | id => exact ComputableInPolyTime.id'
  | comp _ _ firstPoly secondPoly => exact firstPoly.trans secondPoly
  | @fst left right =>
    exact (ComputableInPolyTime.fst (encodeTy left) (encodeTy right)).of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | @snd left right =>
    exact (ComputableInPolyTime.snd (encodeTy left) (encodeTy right)).of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | pair _ _ leftPoly rightPoly => exact leftPoly.prod rightPoly
  | const _ value => exact ComputableInPolyTime.const value
  | branch _ _ _ guardPoly yesPoly noPoly => exact guardPoly.ite yesPoly noPoly
  | natAdd =>
    exact ComputableInPolyTime.binary_add.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | natSub =>
    exact ComputableTidilyInPolyTime.binary_sub.computableInPolyTime.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | natMul =>
    exact (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
      (ComputableInPolyTime.snd encNat encNat)).of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | natLe =>
    exact ComputableInPolyTime.binary_le.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | @listLen element => exact ComputableInPolyTime.length_list_binary (encodeTy element)
  | listMap _ elementPoly => exact ComputableInPolyTime.map elementPoly
  | boolNot => exact ComputableInPolyTime.bool_not
  | boolAnd =>
    exact ComputableInPolyTime.bool_and.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | boolOr =>
    exact ComputableInPolyTime.bool_or.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | natEq =>
    exact (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
      (ComputableInPolyTime.snd encNat encNat)).of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | listSingle =>
    exact ComputableInPolyTime.cons' ComputableInPolyTime.id'
      (ComputableInPolyTime.const [])
  | @listAppend element =>
    exact (ComputableTidilyInPolyTime.listAppend (encodeTy element)).computableInPolyTime.of_enc_eq
      (by
        rintro ⟨_, _⟩
        rfl)
  | @listJoin element =>
    exact (ComputableTidilyInPolyTime.flatten (encodeTy element)).computableInPolyTime
  | listFilter _ predicatePoly => exact ComputableInPolyTime.filter predicatePoly
  | @listMapEnv env element _ _ callbackPoly =>
    have envPoly := ComputableInPolyTime.fst (encodeTy env) (encList (encodeTy element))
    have listPoly := ComputableInPolyTime.snd (encodeTy env) (encList (encodeTy element))
    exact (ComputableTidilyInPolyTime.mapWith callbackPoly.tidy envPoly.tidy
      listPoly.tidy).computableInPolyTime.of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | @listEnum element =>
    -- Frontier's enumerator emits unary indices. Convert them before serializing the result.
    have convertIndex := (ComputableInPolyTime.fst (encodeTy element) encUnary).prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd (encodeTy element) encUnary))
    have enumerate := (ComputableInPolyTime.zipIdx (encodeTy element)).trans
      (ComputableInPolyTime.map convertIndex)
    refine enumerate.of_enc_eq fun xs => ?_
    change encList (encPair (encodeTy element) encNat) xs.zipIdx =
      encList (encPair (encodeTy element) encNat) (xs.zipIdx.map (fun p => (p.1, p.2)))
    rw [List.map_id'']
    intro _
    rfl
  | listSum => exact ComputableInPolyTime.binary_sum
  | @natPowLen element =>
    have basePoly := ComputableInPolyTime.fst encNat (encList (encodeTy element))
    have listPoly := ComputableInPolyTime.snd encNat (encList (encodeTy element))
    have exponentPoly := (ComputableInPolyTime.length_list (encodeTy element)).comp listPoly
    exact (ComputableInPolyTime.binary_pow' basePoly exponentPoly).of_enc_eq (by
      rintro ⟨_, _⟩
      rfl)
  | @listNth element =>
    let enc := encodeTy element
    have input := ComputableInPolyTime.fst (encList enc) encNat
    have index := ComputableInPolyTime.snd (encList enc) encNat
    have wrap := ComputableInPolyTime.cons' (ComputableInPolyTime.id' (encIn := enc))
      (ComputableInPolyTime.const [])
    exact ComputableInPolyTime.listGetD_binary (encA := encList enc) [] ((ComputableInPolyTime.map wrap).comp input) index
  | boolNe => exact ComputableInPolyTime.bool_xor
  | ofPolyTime _ hf => exact hf

/-- Enumerate the Cartesian product of two lists, in left-list order. -/
def cross {σ τ : Ty} : Code (.pair (.list σ) (.list τ)) (.list (.pair σ τ)) :=
  .comp (.pair .snd .fst) (.comp (.listMapEnv (.comp (.pair .snd .fst) (.listMapEnv .id))) .listJoin)

/-- Compare a pair of binary natural inputs by strict inequality. -/
def natLt : Code (.pair .nat .nat) .bool :=
  .comp (.comp (.pair .snd .fst) .natLe) .boolNot

/-- Prepend the value of a program to the list returned by another program. -/
def cons (a : Code s t) (l : Code s (.list t)) : Code s (.list t) :=
  .comp (.pair (.comp a .listSingle) l) .listAppend

/-- Add the binary natural outputs of two programs on the same input. -/
def add (a b : Code s .nat) : Code s .nat := .comp (.pair a b) .natAdd

/-- Multiply the binary natural outputs of two programs on the same input. -/
def mul (a b : Code s .nat) : Code s .nat := .comp (.pair a b) .natMul

/-- Compare the binary natural outputs of two programs by strict inequality. -/
def lt (a b : Code s .nat) : Code s .bool := .comp (.pair a b) natLt

/-- Conjoin the Boolean outputs of two programs on the same input. -/
def and (a b : Code s .bool) : Code s .bool := .comp (.pair a b) .boolAnd

/-- Append the list outputs of two programs on the same input. -/
def append (a b : Code s (.list t)) : Code s (.list t) := .comp (.pair a b) .listAppend

/-- Enumerate the positions of a list, starting at zero. -/
def indices {τ : Ty} : Code (.list τ) (.list .nat) := .comp .listEnum (.listMap .snd)

/-- Test whether the list returned by a program is empty. -/
def isNil (l : Code s (.list t)) : Code s .bool :=
  .comp (.pair (.comp l .listLen) (.const .nat 0)) .natEq

end Code

theorem natLt_eval (a b : Nat) : Code.natLt.eval (a, b) = decide (a < b) := by
  change (!decide (b ≤ a)) = decide (a < b)
  simp [← decide_not]

theorem natLt_eval_true (a b : Nat) : Code.natLt.eval (a, b) = true ↔ a < b := by
  rw [natLt_eval, decide_eq_true_eq]

theorem isNil_eval_true {s t : Ty} (l : Code s (.list t)) (x : s.denote) :
    (Code.isNil l).eval x = true ↔ l.eval x = [] := by
  change decide ((l.eval x).length = 0) = true ↔ l.eval x = []
  simp

theorem indices_eval {t : Ty} (l : List t.denote) :
    (Code.indices (τ := t)).eval l = List.range l.length := by
  exact (List.zipIdx_map_snd 0 l).trans List.range_eq_range'.symm

theorem listNth_eval {τ : Ty} {l : List τ.denote} {i : Nat} (h : i < l.length) :
    (Code.listNth (τ := τ)).eval (l, i) = [l[i]] := by
  change (l.map fun a => [a]).getD i [] = _
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem listNth_eval_of_le {τ : Ty} {l : List τ.denote} {i : Nat} (h : l.length ≤ i) :
    (Code.listNth (τ := τ)).eval (l, i) = [] := by
  change (l.map fun a => [a]).getD i [] = []
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem map_zipIdx_eq_ofFn {α β : Type} (l : List α) (f : α → Nat → β) :
    l.zipIdx.map (fun x => f x.1 x.2) = List.ofFn (fun i : Fin l.length => f l[i.val] i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have h : i < l.length := by simpa using hi
  simp

end CliffordComplexity
