/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridProblems.Encoding

/-!
# Validity

Polynomial-time validity and equality checks for the signed binary coordinate encoding.
-/

@[expose] public section

namespace GridProblems.GridCode
open CliffordComplexity

/-- Equality of integers represented as differences, including noncanonical pairs. -/
def signedEq : Code (.pair SignedTy SignedTy) .bool :=
  .comp (.pair (Code.add (.comp .fst .fst) (.comp .snd .snd))
    (Code.add (.comp .snd .fst) (.comp .fst .snd))) .natEq

def pointEq : Code (.pair PointTy PointTy) .bool :=
  Code.and (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) signedEq)
    (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) signedEq)

theorem signedEq_eval (p q : Nat × Nat) : signedEq.eval (p, q) = true ↔ integer p = integer q := by
  change decide (p.1 + q.2 = q.1 + p.2) = true ↔ _
  rw [decide_eq_true_eq]
  unfold integer
  omega

theorem pointEq_eval (p q : (Nat × Nat) × (Nat × Nat)) :
    pointEq.eval (p, q) = true ↔ decoded p = decoded q := by
  change (signedEq.eval (p.1, q.1) && signedEq.eval (p.2, q.2)) = true ↔ _
  rw [Bool.and_eq_true, signedEq_eval, signedEq_eval]
  change (_ = _ ∧ _ = _) ↔ (integer p.1, integer p.2) = (integer q.1, integer q.2)
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

abbrev IndexedPointTy := Ty.pair PointTy .nat

def distinctPair : Code (.pair IndexedPointTy IndexedPointTy) .bool :=
  .branch (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq) (.const .bool true)
    (.comp (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) pointEq) .boolNot)

def uniqueCode : Code (.list PointTy) .bool :=
  .comp (.comp (.pair .listEnum .listEnum) Code.cross)
    (.comp (.listMap distinctPair) allCode)

def validCode : Code InputTy .bool :=
  Code.and (Code.lt (.const .nat 0) (.comp .fst .listLen))
    (Code.and (Code.lt .snd (.comp .fst .listLen)) (.comp .fst uniqueCode))

theorem distinctPair_eval (p q : IndexedPointTy.denote) :
    distinctPair.eval (p, q) = true ↔ (decoded p.1 = decoded q.1 → p.2 = q.2) := by
  change (if decide (p.2 = q.2) then true else !(pointEq.eval (p.1, q.1))) = true ↔ _
  by_cases h : p.2 = q.2
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, not_false_eq_true, ite_eq_right,
      Bool.not_eq_true', ← Bool.not_eq_true]
    have he := pointEq_eval p.1 q.1
    cases hc : pointEq.eval (p.1, q.1) <;> simp_all

theorem zipIdx_ofFn {α : Type} {n : Nat} (f : Fin n → α) :
    (List.ofFn f).zipIdx = List.ofFn (fun i => (f i, i.val)) := by
  apply List.ext_getElem <;> simp

theorem uniqueCode_eval {n : Nat} (p : Fin n → PointTy.denote) :
    uniqueCode.eval (List.ofFn p) = true ↔ Function.Injective (decoded ∘ p) := by
  change allCode.eval (((List.ofFn p).zipIdx.map fun a =>
    (List.ofFn p).zipIdx.map (fun b => (a, b))).flatten.map distinctPair.eval) = true ↔ _
  rw [allCode_eval, zipIdx_ofFn]
  simp only [List.forall_mem_map, List.forall_mem_flatten, List.forall_mem_ofFn_iff]
  constructor
  · intro h i j he
    exact Fin.ext ((distinctPair_eval _ _).mp (h i j) he)
  · intro h i j
    apply (distinctPair_eval _ _).mpr
    intro he
    exact congrArg Fin.val (h he)

theorem validCode_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    validCode.eval (input p last) = true ↔ Function.Injective (decoded ∘ p) := by
  change (Code.natLt.eval (0, (List.ofFn p).length) &&
    (Code.natLt.eval (last.val, (List.ofFn p).length) && uniqueCode.eval (List.ofFn p))) = true ↔ _
  rw [List.length_ofFn, natLt_eval, natLt_eval]
  simp only [Nat.zero_lt_succ, decide_true, last.isLt, Bool.true_and]
  exact uniqueCode_eval p

def Valid (x : InputTy.denote) : Prop := ∃ (m : Nat) (p : Fin (m + 1) → PointTy.denote)
  (last : Fin (m + 1)), x = input p last ∧ Function.Injective (decoded ∘ p)

theorem validCode_correct (x : InputTy.denote) : validCode.eval x = true ↔ Valid x := by
  constructor
  · intro h
    have hlen : 0 < x.1.length := by
      change (Code.natLt.eval (0, x.1.length) && _) = true at h
      exact (natLt_eval_true _ _).mp (Bool.and_eq_true_iff.mp h).1
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
    have he : x.2 < x.1.length := by
      change (_ && (Code.natLt.eval (x.2, x.1.length) && _)) = true at h
      exact (natLt_eval_true _ _).mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    let p : Fin (m + 1) → PointTy.denote := fun i => x.1[i.val]'(by omega)
    let last : Fin (m + 1) := ⟨x.2, by simpa only [hm] using he⟩
    have hp : List.ofFn p = x.1 := by
      apply List.ext_getElem
      · simp only [List.length_ofFn]; omega
      · intro i h1 h2
        simp only [List.getElem_ofFn, p]
    have hx : x = input p last := by
      change x = (List.ofFn p, x.2)
      rw [hp]
    refine ⟨m, p, last, hx, ?_⟩
    rw [hx] at h
    exact (validCode_eval p last).mp h
  · rintro ⟨m, p, last, rfl, hp⟩
    exact (validCode_eval p last).mpr hp

end GridProblems.GridCode
