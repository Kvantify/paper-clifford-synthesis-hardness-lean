/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GridCompiler
public import CliffordSynthesis.MatrixAdequacy

/-!
# Grid Adequacy

Evaluation lemmas for the compiled neighborhood, window and coordinate programs
used by the grid-to-tableau reduction.
-/

public section

open GridProblems GridProblems.GridCode

set_option backward.isDefEq.respectTransparency false

namespace CliffordSynthesis.GridCompiler
open CliffordComplexity
open MatrixCompiler

variable {m : Nat}

@[simp] theorem widthPad_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    widthPad.eval (input p last) = List.replicate (2 * m) false := by
  change (((tailCode PointTy).eval (List.ofFn p)).map (fun _ => List.replicate 2 false)).flatten = _
  rw [tailCode_eval]
  simp only [List.ofFn_succ, List.tail_cons, List.map_ofFn, Function.comp_def, List.ofFn_const]
  exact (List.flatten_replicate_replicate (n := m) (m := 2)).trans (by rw [Nat.mul_comm])

@[simp] theorem copyPad_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    copyPad.eval (input p last) = List.replicate (6 * m + 1) false := by
  change false :: (((tailCode PointTy).eval (List.ofFn p)).map
    (fun _ => List.replicate 6 false)).flatten = _
  rw [tailCode_eval]
  simp only [List.ofFn_succ, List.tail_cons, List.map_ofFn, Function.comp_def, List.ofFn_const]
  rw [List.flatten_replicate_replicate, Nat.mul_comm, List.replicate_succ]

theorem axisBit_eval (s p : Nat × Nat) (m j : Nat) :
    axisBit.eval ((s, m), (p, j)) =
      (decide (j < (integer p - integer s + m).toNat) ^^ decide (j < m)) := by
  change Code.boolNe.eval
    (Code.natLt.eval (j + p.2 + s.1, p.1 + s.2 + m), Code.natLt.eval (j, m)) = _
  rw [boolNe_eq_xor, natLt_eval, natLt_eval]
  have h : j + p.2 + s.1 < p.1 + s.2 + m ↔ j < (integer p - integer s + m).toNat := by
    unfold integer
    omega
  simp only [h]

theorem axisWithin_eval (s p : Nat × Nat) (m : Nat) :
    axisWithin.eval ((s, m), p) = true ↔
      -(m : Int) ≤ integer p - integer s ∧ integer p - integer s ≤ m := by
  change (decide (s.1 + p.2 ≤ p.1 + s.2 + m) &&
    decide (p.1 + s.2 ≤ s.1 + p.2 + m)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  unfold integer
  rcases s with ⟨sa, sb⟩
  rcases p with ⟨pa, pb⟩
  dsimp
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor
  all_goals omega

theorem pointWithin_eval (s p : (Nat × Nat) × (Nat × Nat)) (m : Nat) :
    pointWithin.eval ((s, m), p) = true ↔
      (-(m : Int) ≤ (decoded p).1 - (decoded s).1 ∧ (decoded p).1 - (decoded s).1 ≤ m) ∧
      (-(m : Int) ≤ (decoded p).2 - (decoded s).2 ∧ (decoded p).2 - (decoded s).2 ≤ m) := by
  change (axisWithin.eval ((s.1, m), p.1) && axisWithin.eval ((s.2, m), p.2)) = true ↔ _
  rw [Bool.and_eq_true, axisWithin_eval, axisWithin_eval]
  rfl

theorem windowTest_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    windowTest.eval (input p last) = true ↔ BoundedGrid.InWindow (decoded ∘ p) := by
  change allCode.eval ((List.ofFn p).map (fun q => pointWithin.eval ((start.eval (input p last),
    count.eval (input p last)), q))) = true ↔ _
  rw [start_eval, count_eval, allCode_eval]
  simp only [List.forall_mem_map, List.forall_mem_ofFn_iff]
  exact forall_congr' (fun i => pointWithin_eval (p 0) (p i) m)

theorem pointBits_eval (s p : (Nat × Nat) × (Nat × Nat)) (m : Nat) :
    pointBits.eval ((s, (m, List.range (2 * m))), p) =
      (List.ofFn fun j : Fin (2 * m) =>
        decide (j.val < (integer p.1 - integer s.1 + m).toNat) ^^ decide (j.val < m)) ++
      (List.ofFn fun j : Fin (2 * m) =>
        decide (j.val < (integer p.2 - integer s.2 + m).toNat) ^^ decide (j.val < m)) := by
  change ((List.range (2 * m)).map (fun j => axisBit.eval ((s.1, m), (p.1, j)))) ++
    ((List.range (2 * m)).map (fun j => axisBit.eval ((s.2, m), (p.2, j)))) = _
  simp only [axisBit_eval s.1 p.1 m, axisBit_eval s.2 p.2 m]
  rw [range_map, range_map]

@[simp] theorem bool_bit (b : Bool) : EncodedTarget.bool (LocalChart.bit b) = b := by
  cases b <;> rfl

theorem bits_as_list (p : Fin (m + 1) → PointTy.denote) (i : Fin (m + 1)) :
    pointBits.eval ((p 0, (m, List.range (2 * m))), p i) =
      encodeRow (BoundedGrid.vertex (decoded ∘ p) i) := by
  rw [pointBits_eval]
  unfold encodeRow BoundedGrid.vertex
  simp only [bool_bit]
  rw [List.ofFn_add]
  congr 1 <;> apply congrArg List.ofFn <;> funext j
  · change _ = BoundedGrid.bits (decoded ∘ p) i (Fin.castAdd (2 * m) j)
    simp [BoundedGrid.bits, BoundedGrid.raw, BoundedGrid.shifted, GridEmbedding.translate,
      GridEmbedding.encode, GridEmbedding.unary, decoded, -Fin.natAdd_eq_addNat]
  · simp [BoundedGrid.bits, BoundedGrid.raw, BoundedGrid.shifted, GridEmbedding.translate,
      GridEmbedding.encode, GridEmbedding.unary, decoded, -Fin.natAdd_eq_addNat]

theorem vertices_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    vertices.eval (input p last) = List.ofFn (fun i => encodeRow (BoundedGrid.vertex (decoded ∘ p) i)) := by
  change (List.ofFn p).map (fun q => pointBits.eval ((start.eval (input p last),
    (count.eval (input p last), Code.indices.eval (widthPad.eval (input p last)))), q)) = _
  rw [start_eval, count_eval, widthPad_eval, indices_eval]
  simp only [List.length_replicate, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext i
  exact bits_as_list p i

theorem repeated_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    repeated.eval (input p last) = List.ofFn (fun a => encodeRow
      (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m) a)) := by
  change ((vertices.eval (input p last)).map (fun v => (copyPad.eval (input p last)).map (fun _ => v))).flatten = _
  rw [vertices_eval, copyPad_eval]
  simp only [List.map_replicate, List.map_ofFn]
  conv_rhs => rw [List.ofFn_mul (m := m + 1) (n := 6 * m + 1)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_def]
  rw [← List.ofFn_const]
  apply congrArg List.ofFn
  funext j
  congr 1
  apply congrArg (BoundedGrid.vertex (decoded ∘ p))
  apply Fin.ext
  change i.val = (i.val * (6 * m + 1) + j.val) / (6 * m + 1)
  simp [Nat.add_div, Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt]
  omega

theorem endBits_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    endBits.eval (input p last) = encodeRow (BoundedGrid.vertex (decoded ∘ p) last) := by
  change (Code.listNth.eval (vertices.eval (input p last), last.val)).flatten = _
  rw [vertices_eval, listNth_eval (τ := RowTy) (by simpa using last.isLt)]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.getElem_ofFn]

theorem template_eval (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    template.eval (input p last) =
      ((encodeRow (BoundedGrid.vertex (decoded ∘ p) last), List.ofFn (fun a => encodeRow
        (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m) a))),
       EncodedTarget.recorderCount m + m) := by
  change ((endBits.eval (input p last), repeated.eval (input p last)),
    (repeated.eval (input p last)).length + count.eval (input p last)) = _
  rw [endBits_eval, repeated_eval, count_eval, List.length_ofFn]

end CliffordSynthesis.GridCompiler
