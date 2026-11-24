/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.ListPrograms
public import CslibFrontier.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Sigma

/-!
# Positive SAT

Variable labels and syntax certificates used to connect the positive exact-one-in-three SAT
language to the compiled grid reduction.
-/

public section

namespace CliffordComplexity
open Cslib.Logic.PL Turing.MultiTapeTM
variable {α : Type}

abbrev ClauseTy : Ty := .list (.pair .nat .bool)
abbrev SatTy : Ty := .list ClauseTy

/-- Collect first occurrences of the variable labels in formula order. -/
@[expose] def vsOf (x : SatTy.denote) : List Nat :=
  let labels := (x.flatten.map Prod.fst : List Nat)
  ((labels.zipIdx).filter (fun p => decide (labels.idxOf p.1 = p.2))).map Prod.fst

private def firstPosition : Code (.pair (.list .nat) (.pair .nat .nat)) .bool :=
  .comp (.pair (.comp (.pair .fst (.comp .snd .fst)) Code.labelIndex) (.comp .snd .snd)) .natEq

def varsCode : Code SatTy (.list .nat) :=
  let labels : Code SatTy (.list .nat) := .comp .listJoin (.listMap .fst)
  .comp (.pair labels (.comp labels .listEnum)) (firstPosition.filterMapEnv (.comp .snd .fst))

theorem varsCode_eval (x : SatTy.denote) : varsCode.eval x = vsOf x := by
  let labels := (x.flatten.map Prod.fst : List Nat)
  change (firstPosition.filterMapEnv (.comp .snd .fst)).eval (labels, labels.zipIdx) = _
  rw [filterMapEnv_eval]
  rfl

theorem nodup_vsOf (x : SatTy.denote) : (vsOf x).Nodup := by
  let labels := (x.flatten.map Prod.fst : List Nat)
  change (((labels.zipIdx).filter (fun p => decide (labels.idxOf p.1 = p.2))).map Prod.fst).Nodup
  apply List.Nodup.map_on _ (((List.nodup_zipIdx_map_snd labels).of_map Prod.snd).filter _)
  intro a ha b hb h
  have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
  have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
  exact Prod.ext h (by rw [← ha', ← hb', h])

theorem mem_vsOf (x : SatTy.denote) {v : Nat} : v ∈ vsOf x ↔ v ∈ CNF.vars (V := Nat) x := by
  let labels := CNF.vars (V := Nat) x
  change v ∈ ((labels.zipIdx).filter (fun p => decide (labels.idxOf p.1 = p.2))).map Prod.fst ↔
    v ∈ labels
  constructor
  · rintro hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hp).1
  · intro hv
    have hi := List.idxOf_lt_length_of_mem hv
    refine List.mem_map.mpr ⟨(v, labels.idxOf v), List.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hi]; exact congrArg some (List.idxOf_get hi))

@[expose] def varSlot [DecidableEq α] (l : List α) (v : α) : Fin (l.length + 1) :=
  ⟨l.idxOf v, Nat.lt_succ_of_le List.idxOf_le_length⟩

theorem varSlot_val_of_mem [DecidableEq α] {l : List α} {v : α} (_ : v ∈ l) :
    (varSlot l v).val = l.idxOf v := rfl

theorem varSlot_inj [DecidableEq α] {l : List α} {v w : α} (hv : v ∈ l) (_ : w ∈ l)
    (h : varSlot l v = varSlot l w) : v = w :=
  (List.idxOf_inj hv).mp (congrArg Fin.val h)

@[expose] def slotOfCode : Code (.pair (.list .nat) .nat) .nat := Code.labelIndex

theorem slotOfCode_eval (l : List Nat) (v : Nat) : slotOfCode.eval (l, v) = (varSlot l v).val := rfl

namespace Concrete

/-- Positive formulas of width exactly three, counting occurrences. -/
@[expose] def MONOTONE_ONE_IN_THREE_SAT3 (x : SatTy.denote) : Prop :=
  (∀ c ∈ x, ∀ p ∈ c, p.2 = true) ∧ (∀ c ∈ x, c.length = 3) ∧ CNF.OneSatisfiable (V := Nat) x

theorem monotoneOneInThree3Sat_iff (x : SatTy.denote) :
    MONOTONE_ONE_IN_THREE_SAT3 x ↔
      (∀ c ∈ x, ∀ p ∈ c, p.2 = true) ∧ (∀ c ∈ x, c.length = 3) ∧ CNF.OneSatisfiable (V := Nat) x := Iff.rfl

end Concrete

open Cslib.Complexity

/-- Test the distinct-variable syntax before using an occurrence-based representation. -/
@[expose] def exactThreeToPositive (x : SatTy.denote) : SatTy.denote :=
  if PositiveOneInExactThreeSAT.syntaxCheck x then x else [[]]

theorem positiveExactThreeReduction :
    PolyTimeReducible encCNF (encodeTy SatTy) PositiveOneInExactThreeSAT
      {x | Concrete.MONOTONE_ONE_IN_THREE_SAT3 x} := by
  refine ⟨exactThreeToPositive, ?_, fun x => ?_⟩
  · exact PositiveOneInExactThreeSAT.computableInPolyTime_syntaxCheck.ite
      ComputableInPolyTime.id' (ComputableInPolyTime.const [[]])
  · by_cases h : PositiveOneInExactThreeSAT.syntaxCheck x = true
    · obtain ⟨hclauses, hsign⟩ := (PositiveOneInExactThreeSAT.syntaxCheck_iff x).mp h
      have hp := (OneSAT.positiveCheck_iff x).mp hsign
      have hw : ∀ c ∈ x, c.length = 3 := fun c hc => (hclauses c hc).1
      rw [PositiveOneInExactThreeSAT.mem_iff_syntaxCheck]
      simp only [h, true_and, exactThreeToPositive, ite_eq_left h]
      change CNF.OneSatisfiable (V := Nat) x ↔ _
      exact ⟨fun hx => ⟨hp, hw, hx⟩, fun hx => hx.2.2⟩
    · rw [PositiveOneInExactThreeSAT.mem_iff_syntaxCheck]
      change (_ ∧ _) ↔ Concrete.MONOTONE_ONE_IN_THREE_SAT3 (exactThreeToPositive x)
      rw [exactThreeToPositive, ite_eq_right h]
      exact iff_of_false (fun hx => h hx.1) (fun hx => by have := hx.2.1 [] (by simp); simp at this)

theorem positiveExactOne_npHard : NPHard (encodeTy SatTy) {x | Concrete.MONOTONE_ONE_IN_THREE_SAT3 x} :=
  PositiveOneInExactThreeSAT_npHard.trans positiveExactThreeReduction

end CliffordComplexity
