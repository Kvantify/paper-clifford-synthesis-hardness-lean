/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.MatrixCompiler

/-!
# Matrix Adequacy

Evaluation of the Boolean row compiler on the vector and matrix data that
parameterize the three-block target.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CliffordSynthesis.MatrixCompiler
open Planes (F)
open Target (Wire)

variable {d r : Nat} {α : Type*}

def wireList (f : Wire d r → α) : List α :=
  (List.ofFn fun j => f (.inl j)) ++ [f (.inr (.inl ()))] ++
    (List.ofFn fun a => f (.inr (.inr a)))

theorem wireList_eq (f : Wire d r → α) : wireList f =
    List.ofFn (fun i => f ((EncodedTarget.physicalLabel d r).symm i)) := by
  have hf : (fun i => f ((EncodedTarget.physicalLabel d r).symm i)) =
      Fin.append (fun j => f (.inl j))
        (Fin.append (fun _ : Fin 1 => f (.inr (.inl ()))) (fun a => f (.inr (.inr a)))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun a => ?_) i
    · simp [EncodedTarget.physicalLabel]
    · refine Fin.addCases (fun j => ?_) (fun b => ?_) a
      · fin_cases j
        simp [EncodedTarget.physicalLabel, EncodedTarget.unitFin]
      · simp [EncodedTarget.physicalLabel]
  rw [hf, List.ofFn_fin_append, List.ofFn_fin_append]
  simp [wireList, List.append_assoc]

def encodeRow (f : Fin d → F) : List Bool := List.ofFn (fun j => EncodedTarget.bool (f j))

theorem bool_add (a b : F) : EncodedTarget.bool (a + b) =
    (EncodedTarget.bool a ^^ EncodedTarget.bool b) := by
  have h : ∀ a b : F, EncodedTarget.bool (a + b) =
      (EncodedTarget.bool a ^^ EncodedTarget.bool b) := by decide
  exact h a b

@[simp] theorem bool_zero : EncodedTarget.bool 0 = false := rfl
@[simp] theorem bool_one : EncodedTarget.bool 1 = true := rfl

theorem range_map (f : Nat → α) (n : Nat) : (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

@[simp] theorem readBit_encodeRow (f : Fin d → F) (j : Fin d) :
    readBit (encodeRow f) j.val = EncodedTarget.bool (f j) := by
  simp [readBit, encodeRow, j.isLt]

theorem basis_of_length {l : List α} (hl : l.length = d) (i : Fin d) :
    basis l i.val = List.ofFn (fun j : Fin d => decide (i = j)) := by
  simp only [basis, hl, range_map]
  congr 1

@[simp] theorem zeroes_ofFn (f : Fin d → α) : zeroes (List.ofFn f) = List.ofFn (fun _ : Fin d => false) := by
  simp [zeroes, List.map_ofFn]

@[simp] theorem ones_ofFn (f : Fin d → α) : ones (List.ofFn f) = List.ofFn (fun _ : Fin d => true) := by
  simp [ones, List.map_ofFn]

theorem a_coordinate (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (i : Fin d) :
    wireList (fun j => EncodedTarget.bool (Target.matrix t X (.inl i) j)) =
      basis (encodeRow t) i.val ++ [false] ++ zeroes (List.ofFn fun a => encodeRow (X a)) := by
  rw [basis_of_length (by simp [encodeRow]) i, zeroes_ofFn]
  simp [wireList, Target.matrix, Target.offset, Matrix.one_apply, EncodedTarget.bool]

theorem a_path (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) :
    wireList (fun j => EncodedTarget.bool (Target.matrix t X (.inr (.inl ())) j)) =
      encodeRow t ++ [true] ++ zeroes (List.ofFn fun a => encodeRow (X a)) := by
  rw [zeroes_ofFn]
  simp [wireList, encodeRow, Target.matrix, Target.offset, EncodedTarget.bool]

theorem a_recorder (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (a : Fin r) :
    wireList (fun j => EncodedTarget.bool (Target.matrix t X (.inr (.inr a)) j)) =
      encodeRow (X a) ++ [true] ++ basis (List.ofFn fun a => encodeRow (X a)) a.val := by
  rw [basis_of_length (by simp) a]
  simp [wireList, encodeRow, Target.matrix, Target.offset, Matrix.one_apply, EncodedTarget.bool]

/-- The compiler's X block equals `Target.matrix` in physical wire order. -/
theorem rowA_correct (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) :
    rowA (encodeRow t) (List.ofFn (fun a => encodeRow (X a))) =
      wireList (fun i => wireList (fun j => EncodedTarget.bool (Target.matrix t X i j))) := by
  change _ = (List.ofFn _) ++ [_] ++ (List.ofFn _)
  simp_rw [a_coordinate, a_path, a_recorder]
  unfold rowA
  rw [CliffordComplexity.map_zipIdx_eq_ofFn (List.ofFn fun a => encodeRow (X a))
    (fun x k => x ++ [true] ++ basis (List.ofFn fun a => encodeRow (X a)) k)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  rw [show (encodeRow t).length = d from List.length_ofFn, range_map]
  rfl

 theorem b_coordinate (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (i : Fin d) :
    wireList (fun j => EncodedTarget.bool (Target.inverse t X j (.inl i))) =
      basis (encodeRow t) i.val ++ [EncodedTarget.bool (t i)] ++
        (List.ofFn fun a => EncodedTarget.bool (X a i) ^^ EncodedTarget.bool (t i)) := by
  rw [basis_of_length (by simp [encodeRow]) i]
  simp only [wireList, Target.inverse, Target.offset, Target.squareOffset,
    Matrix.add_apply, Matrix.one_apply, Sum.inl.injEq,
    reduceCtorEq, ite_false, zero_add, add_zero, bool_add]
  congr 2
  apply congrArg List.ofFn
  funext j
  by_cases h : j = i
  · subst j; simp [EncodedTarget.bool]
  · simp [h, Ne.symm h, EncodedTarget.bool]

 theorem b_path (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) :
    wireList (fun j => EncodedTarget.bool (Target.inverse t X j (.inr (.inl ())))) =
      zeroes (encodeRow t) ++ [true] ++ ones (List.ofFn fun a => encodeRow (X a)) := by
  simp [wireList, encodeRow, zeroes, ones, Target.inverse, Target.offset,
    Target.squareOffset, EncodedTarget.bool]

 theorem b_recorder (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (a : Fin r) :
    wireList (fun j => EncodedTarget.bool (Target.inverse t X j (.inr (.inr a)))) =
      zeroes (encodeRow t) ++ [false] ++ basis (List.ofFn fun a => encodeRow (X a)) a.val := by
  rw [basis_of_length (by simp) a]
  simp [wireList, encodeRow, zeroes, Target.inverse, Target.offset,
    Target.squareOffset, Matrix.one_apply, EncodedTarget.bool, eq_comm]

/-- The emitted Z block is the transpose of the explicit inverse. -/
theorem rowB_correct (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) :
    rowB (encodeRow t) (List.ofFn (fun a => encodeRow (X a))) =
      wireList (fun i => wireList (fun j => EncodedTarget.bool (Target.inverse t X j i))) := by
  change _ = (List.ofFn _) ++ [_] ++ (List.ofFn _)
  simp_rw [b_coordinate, b_path, b_recorder]
  unfold rowB
  rw [show (encodeRow t).length = d from List.length_ofFn]
  simp only [List.length_ofFn, range_map, List.map_ofFn]
  congr 2
  apply congrArg List.ofFn
  funext i
  simp [readBit_encodeRow, Function.comp_def]

end CliffordSynthesis.MatrixCompiler
