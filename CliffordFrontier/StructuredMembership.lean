/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.DecisionProblems
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Structured Membership

A polynomial verifier for the three-block target restriction. The witness supplies
the Boolean vector and the recorder matrix from [FugledeJorgensen2026].
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordComplexity CliffordSynthesis
open CliffordSynthesis.MatrixCompiler Turing.MultiTapeTM

private def rectangular (w : TemplateTy.denote) : Bool :=
  w.2.all (fun row => decide (row.length = w.1.length))

private theorem rectangular_polyTime : ComputableInPolyTime rectangular (encodeTy TemplateTy) encBool := by
  let rowLength := ComputableInPolyTime.length_list_binary encBool
  have rows := ComputableTidilyInPolyTime.snd (encodeTy RowTy) (encodeTy MatrixTy)
  have width := rowLength.comp (ComputableInPolyTime.fst (encodeTy RowTy) (encodeTy MatrixTy))
  have checkRow := (rowLength.comp (ComputableInPolyTime.snd (encodeTy TemplateTy) (encodeTy RowTy))).decide_eq'
    (width.comp (ComputableInPolyTime.fst (encodeTy TemplateTy) (encodeTy RowTy)))
  exact (ComputableTidilyInPolyTime.allWithInput rows checkRow.tidy).computableInPolyTime

private def checkStructured (p : SynthesisInput × TemplateTy.denote) : Bool :=
  rectangular p.2 && decide (compile.eval (p.2, p.1.2.2) = p.1)

private theorem checkStructured_polyTime :
    ComputableInPolyTime checkStructured (encPair encSynthesisInput (encodeTy TemplateTy)) encBool := by
  have out := ComputableInPolyTime.fst encSynthesisInput (encodeTy TemplateTy)
  have w := ComputableInPolyTime.snd encSynthesisInput (encodeTy TemplateTy)
  have output := compile.polyTime.comp (w.prod out.snd'.snd')
  exact (rectangular_polyTime.comp w).bool_and' (output.decide_eq' out)

private theorem bool_bit (b : Bool) : EncodedTarget.bool (LocalChart.bit b) = b := by
  cases b <;> rfl

private theorem row_as_values (l : List Bool) :
    encodeRow (fun j : Fin l.length => LocalChart.bit (l.get j)) = l := by
  unfold encodeRow
  conv_rhs => rw [← List.ofFn_get l]
  congr 1
  funext j
  exact bool_bit _

private theorem checkStructured_sound (out : SynthesisInput) (w : TemplateTy.denote)
    (h : checkStructured (out, w) = true) : out ∈ structuredTargets := by
  have hcheck : rectangular w = true ∧ compile.eval (w, out.2.2) = out := by
    simpa only [checkStructured, Bool.and_eq_true, decide_eq_true_eq] using h
  obtain ⟨hr, hout⟩ := hcheck
  have hrow (i : Fin w.2.length) : (w.2.get i).length = w.1.length :=
    of_decide_eq_true (List.all_eq_true.mp hr _ (List.get_mem w.2 i))
  let t (j : Fin w.1.length) := LocalChart.bit (w.1.get j)
  let X (i : Fin w.2.length) (j : Fin w.1.length) :=
    LocalChart.bit ((w.2.get i).get (Fin.cast (hrow i).symm j))
  have hX (i : Fin w.2.length) : encodeRow (X i) = w.2.get i := by
    apply List.ext_getElem
      (show (encodeRow (X i)).length = (w.2.get i).length from
        List.length_ofFn.trans (hrow i).symm)
    intro j hj hq
    simp only [encodeRow, List.getElem_ofFn, X]
    change EncodedTarget.bool (LocalChart.bit ((w.2.get i).get ⟨j, hq⟩)) = _
    exact bool_bit _
  have hw : (encodeRow t, List.ofFn fun i => encodeRow (X i)) = w := by
    apply Prod.ext
    · exact row_as_values w.1
    · simp only [hX, List.ofFn_get]
  refine ⟨_, _, t, X, out.2.2, ?_, Target.nilpotent_target t X, Target.diagonal t X,
    Target.lower_triangular t X, Target.lift_symplectic t X⟩
  have hc := compile_encode t X out.2.2
  rw [hw] at hc
  exact hout.symm.trans hc

theorem structuredTargets_mem_NP : structuredTargets ∈ NP encSynthesisInput := by
  let decoder := Decoder.pair (Decoder.list Decoder.bool) (Decoder.list (Decoder.list Decoder.bool))
  apply mem_NP_of_check (p := 8 * (Polynomial.X + 1) ^ 2) decoder
    checkStructured_polyTime checkStructured_sound
  rintro out ⟨d, r, t, X, k, rfl, _, _, _, _⟩
  let w : TemplateTy.denote := (encodeRow t, List.ofFn fun i => encodeRow (X i))
  refine ⟨w, ?_, ?_⟩
  · simp only [checkStructured, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · apply List.all_eq_true.mpr
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      simp [w, encodeRow]
    · exact compile_encode t X k
  · let out := encode (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k
    have hn : d + (1 + r) ≤ (encSynthesisInput out).length := by
      change d + (1 + r) ≤ (encPair (encodeTy MatrixTy) (encodeTy (.pair MatrixTy .nat)) out).length
      have h := (length_le_length_encList (encList encBool) out.1).trans
        (length_le_encPair_left (encodeTy MatrixTy) (encodeTy (.pair MatrixTy .nat)) out)
      simpa only [out, encode, List.length_ofFn] using h
    have rowBound (a : Fin d → Planes.F) : (encList encBool (encodeRow a)).length ≤ 3 * d := by
      simpa [encodeRow, Nat.mul_comm] using
        (length_encList_le encBool (encodeRow a) (b := 1) (by simp [encBool_apply]))
    have matrixBound :
        (encList (encList encBool) w.2).length ≤ r * (2 * (3 * d) + 1) := by
      simpa only [w, List.length_ofFn] using
        (length_encList_le (encList encBool) w.2 (b := 3 * d) fun l hl => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
          exact rowBound (X i))
    change (encPair (encList encBool) (encList (encList encBool)) w).length ≤ _
    rw [length_encPair]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    calc
      _ ≤ 2 * (3 * d) + 1 + r * (2 * (3 * d) + 1) := by
        exact Nat.add_le_add (by have := rowBound t; simp only [w]; omega) matrixBound
      _ ≤ 8 * ((encSynthesisInput out).length + 1) ^ 2 := by
        have hd : d ≤ (encSynthesisInput out).length := by omega
        have hr : r ≤ (encSynthesisInput out).length := by omega
        have hdr := Nat.mul_le_mul hr hd
        nlinarith

end CliffordFrontier
