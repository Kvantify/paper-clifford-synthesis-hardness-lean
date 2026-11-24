/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Problems
public import CliffordSynthesis.Certificates
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Quadratic CNOT synthesis bound

A quadratic CNOT count bound for block-diagonal tableau targets.

The bounded diagonalization argument adapts Mathlib's `Matrix.Pivot` proofs
in `Mathlib.LinearAlgebra.Matrix.Transvection` by Sébastien Gouëzel (Apache 2.0).
It records how many transvections the elimination uses at each dimension.
-/

public section

namespace CliffordFrontier

open CliffordSynthesis Matrix TransvectionStruct

section Elimination

variable {K : Type} [Field K]

private theorem clear_with_pivot {r : Nat} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K)
    (hM : M (.inr ()) (.inr ()) ≠ 0) :
    ∃ L R : List (TransvectionStruct (Fin r ⊕ Unit) K),
      L.length = r ∧ R.length = r ∧
        IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (R.map toMatrix).prod) := by
  let L : List (TransvectionStruct (Fin r ⊕ Unit) K) :=
    List.ofFn fun i : Fin r =>
      ⟨.inl i, .inr (), by simp, -M (.inl i) (.inr ()) / M (.inr ()) (.inr ())⟩
  let R : List (TransvectionStruct (Fin r ⊕ Unit) K) :=
    List.ofFn fun i : Fin r =>
      ⟨.inr (), .inl i, by simp, -M (.inr ()) (.inl i) / M (.inr ()) (.inr ())⟩
  refine ⟨L, R, by simp [L], by simp [R], ?_⟩
  have hl : L.map toMatrix = Pivot.listTransvecCol M := by simp [L, Pivot.listTransvecCol, Function.comp_def]
  have hr : R.map toMatrix = Pivot.listTransvecRow M := by simp [R, Pivot.listTransvecRow, Function.comp_def]
  rw [hl, hr]
  exact Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

private theorem clear_last_row_column {r : Nat} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) K) :
    ∃ L R : List (TransvectionStruct (Fin r ⊕ Unit) K),
      L.length + R.length ≤ 2 * r + 1 ∧
        IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (R.map toMatrix).prod) := by
  classical
  by_cases hb : IsTwoBlockDiagonal M
  · exact ⟨[], [], by simp, by simpa using hb⟩
  by_cases hM : M (.inr ()) (.inr ()) = 0
  · have hnonzero : ∃ i : Fin r, M (.inl i) (.inr ()) ≠ 0 ∨ M (.inr ()) (.inl i) ≠ 0 := by
      simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at hb
      rcases hb with hl | hr
      · contrapose! hl
        rintro i ⟨⟩
        exact (hl i).1
      · contrapose! hr
        rintro ⟨⟩ i
        exact (hr i).2
    obtain ⟨i, hi | hi⟩ := hnonzero
    · let pivot : TransvectionStruct (Fin r ⊕ Unit) K := ⟨.inr (), .inl i, by simp, 1⟩
      let M' := pivot.toMatrix * M
      have hM' : M' (.inr ()) (.inr ()) ≠ 0 := by simpa [M', pivot, hM]
      obtain ⟨L, R, hL, hR, hb⟩ := clear_with_pivot M' hM'
      refine ⟨L ++ [pivot], R, by simp [hL, hR]; omega, ?_⟩
      simpa [M', Matrix.mul_assoc] using hb
    · let pivot : TransvectionStruct (Fin r ⊕ Unit) K := ⟨.inl i, .inr (), by simp, 1⟩
      let M' := M * pivot.toMatrix
      have hM' : M' (.inr ()) (.inr ()) ≠ 0 := by simpa [M', pivot, hM]
      obtain ⟨L, R, hL, hR, hb⟩ := clear_with_pivot M' hM'
      refine ⟨L, pivot :: R, by simp [hL, hR]; omega, ?_⟩
      simpa [M', Matrix.mul_assoc] using hb
  · obtain ⟨L, R, hL, hR, hb⟩ := clear_with_pivot M hM
    exact ⟨L, R, by omega, hb⟩

private theorem bounded_diagonalization {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    ∃ (L R : List (TransvectionStruct n K)) (d : n → K),
      L.length + R.length ≤ (Fintype.card n)^2 ∧
        (L.map toMatrix).prod * M * (R.map toMatrix).prod = diagonal d := by
  suffices ∀ k, Fintype.card n = k →
      ∃ (L R : List (TransvectionStruct n K)) (d : n → K),
        L.length + R.length ≤ k^2 ∧
          (L.map toMatrix).prod * M * (R.map toMatrix).prod = diagonal d by
    exact this _ rfl
  intro k hk
  induction k generalizing n M with
  | zero =>
    refine ⟨[], [], fun _ => 1, by simp, ?_⟩
    ext i j
    exact (Fintype.card_eq_zero_iff.mp hk).elim' i
  | succ r ih =>
    let e : n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [hk])
    let A := reindexAlgEquiv K _ e M
    obtain ⟨L₁, R₁, hlen₁, hblock⟩ := clear_last_row_column A
    let B := (L₁.map toMatrix).prod * A * (R₁.map toMatrix).prod
    let B₀ := toBlocks₁₁ B
    obtain ⟨L₀, R₀, d₀, hlen₀, hdiag⟩ := ih B₀ (by simp)
    let L := L₀.map (sumInl Unit) ++ L₁
    let R := R₁ ++ R₀.map (sumInl Unit)
    let d : Fin r ⊕ Unit → K := Sum.elim d₀ (fun _ => B (.inr ()) (.inr ()))
    have hB : B = fromBlocks B₀ 0 0 (diagonal fun _ => B (.inr ()) (.inr ())) := by
      rw [← fromBlocks_toBlocks B, hblock.1, hblock.2]
      rfl
    have hdiagA : (L.map toMatrix).prod * A * (R.map toMatrix).prod = diagonal d := by
      suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * B *
          (R₀.map (toMatrix ∘ sumInl Unit)).prod = diagonal d by
        simpa [L, R, B, Matrix.mul_assoc]
      conv_lhs => rw [hB]
      simp [hdiag, d]
    refine ⟨L.map (reindexEquiv e.symm), R.map (reindexEquiv e.symm), d ∘ e, ?_, ?_⟩
    · simp only [L, R, List.length_map, List.length_append]
      nlinarith
    · have hA : M = reindexAlgEquiv K _ e.symm A := by simp [A]
      rw [hA]
      simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, hdiagA]
      simp

theorem bounded_transvection_factorization {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    ∃ (L R : List (TransvectionStruct n K)) (d : n → K),
      L.length + R.length ≤ (Fintype.card n)^2 ∧
        M = (L.map toMatrix).prod * diagonal d * (R.map toMatrix).prod := by
  obtain ⟨L, R, d, hlen, hdiag⟩ := bounded_diagonalization M
  refine ⟨L.reverse.map TransvectionStruct.inv, R.reverse.map TransvectionStruct.inv,
    d, by simpa using hlen, ?_⟩
  suffices M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((R.map toMatrix).prod * (R.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) by
    simpa [← hdiag, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Elimination

section LinearSynthesis

open Planes (F)
open CliffordSynthesis.RowExtraction (AddGate)
open CliffordSynthesis.RowHistory (asCircuit)
open CliffordSynthesis.MatrixCompiler (OutputTy decode Accepts)

private def xBlock {n : Nat} (a : Circuit.Tableau n) : Matrix (Fin n) (Fin n) F :=
  fun i j => LocalChart.bit (a.x i (j, false))

private def zBlock {n : Nat} (a : Circuit.Tableau n) : Matrix (Fin n) (Fin n) F :=
  fun i j => LocalChart.bit (a.z i (j, true))

private def BlockDiagonal {n : Nat} (a : Circuit.Tableau n) : Prop :=
  ∀ i j, a.x i (j, true) = false ∧ a.z i (j, false) = false

private theorem xBlock_identity (n : Nat) : xBlock (Circuit.identity n) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [xBlock, Circuit.identity, Matrix.one_apply, LocalChart.bit, h]

private theorem xBlock_cnot {n : Nat} (c t : Fin n) (a : Circuit.Tableau n) :
    xBlock (Circuit.cnot c t a) = transvection t c 1 * xBlock a := by
  ext i j
  by_cases h : i = t
  · subst i
    simp [xBlock, Circuit.cnot, LocalChart.bit_xor]
  · simp [xBlock, Circuit.cnot, h]

private def matrixOfGate {n : Nat} (g : AddGate n) : Matrix (Fin n) (Fin n) F :=
  transvection g.target g.control 1

private theorem xBlock_run {n : Nat} (gs : List (AddGate n)) (a : Circuit.Tableau n) :
    xBlock (Circuit.run (asCircuit gs) a) = (gs.reverse.map matrixOfGate).prod * xBlock a := by
  induction gs generalizing a with
  | nil => simp [asCircuit, Circuit.run]
  | cons g gs ih =>
    change xBlock (Circuit.run (asCircuit gs) (Circuit.cnot g.control g.target a)) = _
    rw [ih, xBlock_cnot]
    simp [matrixOfGate, Matrix.mul_assoc]

private theorem transvection_word {n : Nat} (L : List (TransvectionStruct (Fin n) F)) :
    ∃ gs : List (AddGate n), gs.length ≤ L.length ∧
      (gs.map matrixOfGate).prod = (L.map toMatrix).prod := by
  induction L with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons s L ih =>
    obtain ⟨gs, hlen, he⟩ := ih
    have hcases : ∀ a : F, a = 0 ∨ a = 1 := by decide
    rcases hcases s.c with h | h
    · exact ⟨gs, by simp; omega, by simp [he, TransvectionStruct.toMatrix, h]⟩
    · refine ⟨⟨s.j, s.i, s.hij.symm⟩ :: gs, by simp [hlen], ?_⟩
      simp [matrixOfGate, TransvectionStruct.toMatrix, h, he]

private theorem realizes_xBlock {n : Nat} (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    ∃ gs : List (AddGate n), gs.length ≤ n ^ 2 ∧
      xBlock (Circuit.run (asCircuit gs) (Circuit.identity n)) = M := by
  obtain ⟨L, R, d, hlen, hMprod⟩ := bounded_transvection_factorization M
  have hdet : M.det = ∏ i, d i := by
    rw [hMprod]
    simp [Matrix.det_mul, Matrix.det_diagonal]
  have hd : d = fun _ => 1 := by
    funext i
    have hcases : ∀ a : F, a = 0 ∨ a = 1 := by decide
    exact (hcases (d i)).resolve_left fun hz =>
      hM (hdet.trans (Finset.prod_eq_zero (Finset.mem_univ i) hz))
  obtain ⟨gs, hgs, hmat⟩ := transvection_word (L ++ R)
  refine ⟨gs.reverse, ?_, ?_⟩
  · have hlen' : (L ++ R).length ≤ n ^ 2 := by simpa using hlen
    simpa only [List.length_reverse] using hgs.trans hlen'
  · rw [xBlock_run, xBlock_identity, List.reverse_reverse, Matrix.mul_one, hmat, hMprod]
    simp [hd]

private theorem diagonal_cnot_run {n : Nat} (gs : List (AddGate n)) (a : Circuit.Tableau n)
    (ha : BlockDiagonal a) : BlockDiagonal (Circuit.run (asCircuit gs) a) := by
  induction gs generalizing a with
  | nil => exact ha
  | cons g gs ih =>
    apply ih (Circuit.cnot g.control g.target a)
    intro i j
    simp [Circuit.cnot, (ha i j).1, (ha i j).2, (ha g.control j).1, (ha g.target j).2]

private theorem product_of_blocks {n : Nat} {a : Circuit.Tableau n} (hdiag : BlockDiagonal a)
    (h : SymplecticCircuit.IsSymplectic (StandardSpace.form n) (StandardSpace.fieldRows a)) :
    xBlock a * (zBlock a)ᵀ = 1 := by
  ext i j
  have hxz := h.xz i j
  rw [StandardSpace.form_apply] at hxz
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, xBlock, zBlock,
    StandardSpace.fieldRows, fun k => (hdiag i k).1, fun k => (hdiag j k).2, LocalChart.bit] using hxz

private theorem same_of_blocks {n : Nat} {a b : Circuit.Tableau n}
    (ha : BlockDiagonal a) (hb : BlockDiagonal b)
    (hx : xBlock a = xBlock b) (hz : zBlock a = zBlock b) : Circuit.Same a b := by
  have hbit : Function.Injective LocalChart.bit := by decide
  intro i p
  obtain ⟨j, b'⟩ := p
  cases b'
  · exact ⟨hbit (congrFun (congrFun hx i) j), (ha i j).2.trans (hb i j).2.symm⟩
  · exact ⟨(ha i j).1.trans (hb i j).1.symm, hbit (congrFun (congrFun hz i) j)⟩

private theorem tableau_eq_of_same {n : Nat} {a b : Circuit.Tableau n} (h : Circuit.Same a b) :
    a = b := by
  cases a
  cases b
  congr
  · exact funext fun i => funext fun p => (h i p).1
  · exact funext fun i => funext fun p => (h i p).2

/-- Any synthesizable block-diagonal decoded tableau has a CNOT realization
whose length is at most the square of the qubit count. -/
theorem decoded_quadratic_cnot_bound (out : OutputTy.denote) (h : Accepts out) :
    ∃ gs : List (AddGate (decode out).qubits), gs.length ≤ (decode out).qubits ^ 2 ∧
      Circuit.Same (Circuit.run (asCircuit gs) (Circuit.identity (decode out).qubits))
        (decode out).tableau := by
  let n := (decode out).qubits
  let target := (decode out).tableau
  obtain ⟨original, _, hsame⟩ := h
  have htarget : Circuit.run original (Circuit.identity n) = target := tableau_eq_of_same hsame
  have hdiag : BlockDiagonal target := by intro i j; simp [target, decode]
  have hprod : xBlock target * (zBlock target)ᵀ = 1 :=
    product_of_blocks hdiag (htarget ▸ StandardSpace.actual_run_symplectic original)
  obtain ⟨gs, hlen, hx⟩ := realizes_xBlock (xBlock target) (Matrix.isUnit_det_of_right_inverse hprod).ne_zero
  let actual := Circuit.run (asCircuit gs) (Circuit.identity n)
  have hdiagActual : BlockDiagonal actual :=
    diagonal_cnot_run gs _ (fun i j => by simp [Circuit.identity])
  have hprodActual : xBlock actual * (zBlock actual)ᵀ = 1 :=
    product_of_blocks hdiagActual (StandardSpace.actual_run_symplectic (asCircuit gs))
  have hx' : xBlock actual = xBlock target := hx
  rw [hx'] at hprodActual
  have hz : zBlock actual = zBlock target := by
    simpa using congrArg Matrix.transpose (Matrix.right_inv_eq_right_inv hprodActual hprod)
  exact ⟨gs, hlen, same_of_blocks hdiagActual hdiag hx' hz⟩

theorem clifford_at_quadratic_threshold (out : OutputTy.denote) (h : Accepts out) :
    Circuit.SynthesizesWithin (decode out).tableau ((decode out).qubits ^ 2) := by
  obtain ⟨gs, hlen, hsame⟩ := decoded_quadratic_cnot_bound out h
  exact ⟨asCircuit gs, by simpa only [RowHistory.circuit_cost] using hlen, hsame⟩

theorem cnot_only_at_quadratic_threshold (out : OutputTy.denote) (h : CNOTOnly out) :
    HasCNOTCircuit { decode out with threshold := (decode out).qubits ^ 2 } := by
  obtain ⟨gs, hc, hs⟩ := h
  exact decoded_quadratic_cnot_bound out
    ⟨asCircuit gs, by simpa only [RowHistory.circuit_cost] using hc, hs⟩

theorem cnot_only_bounded_witness {out : OutputTy.denote} (h : CNOTOnly out) :
    let inst := decode out
    ∃ gs : List (AddGate inst.qubits), gs.length ≤ inst.threshold ∧ gs.length ≤ inst.qubits ^ 2 ∧
      Circuit.Same (Circuit.run (asCircuit gs) (Circuit.identity inst.qubits)) inst.tableau := by
  obtain ⟨gs, hc, hs⟩ := h
  by_cases hk : (decode out).threshold ≤ (decode out).qubits ^ 2
  · exact ⟨gs, hc, hc.trans hk, hs⟩
  · have ha : Accepts out :=
      ⟨asCircuit gs, by simpa only [RowHistory.circuit_cost] using hc, hs⟩
    obtain ⟨short, hlen, hshort⟩ := decoded_quadratic_cnot_bound out ha
    exact ⟨short, hlen.trans (Nat.le_of_lt (Nat.lt_of_not_ge hk)), hlen, hshort⟩

theorem clifford_bounded_witness {out : OutputTy.denote} (h : Accepts out) :
    let inst := decode out
    let bound := inst.qubits ^ 2
    ∃ gs : List (Circuit.Gate inst.qubits), Circuit.cost gs ≤ inst.threshold ∧
      gs.length ≤ 3 * inst.qubits * (bound + 1) + bound ∧
      Circuit.Same (Circuit.run gs (Circuit.identity inst.qubits)) inst.tableau := by
  obtain ⟨gs, hcost, _, hl, hs⟩ := Certificates.capped_certificate _ _ _ h
    (clifford_at_quadratic_threshold out h)
  exact ⟨gs, hcost, hl, hs⟩

end LinearSynthesis

end CliffordFrontier
