/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalNumbering
public import GridHardness.CorrectedSatIntervalBoundary

/-!
# Corrected SAT Interval Row Numbering

Extend an existing finite numbering through the actual request recursion.
Each crossing appends its own forty names. The construction composes the local
vertex equivalences, without choosing a numbering from a cardinality theorem.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.RowNumbering
open XorLineRegistry XorLineSchedule XorLine

noncomputable def equiv {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height : Nat) (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ i ∈ requests, s.Covered i height) :
    (s.crossRequests a height requests hn hc).Vertex ≃ Fin (N+40*requests.length) :=
  match requests with
  | [] => number.trans (finCongr (by simp))
  | i::is =>
    (equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)).trans
        (finCongr (by simp only [List.length_cons]; omega))

theorem carried_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height : Nat) (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ i ∈ requests, s.Covered i height) (o : Boundary.Outside s a) :
    (equiv s number a height requests hn hc
      (Boundary.carryRequests s a height requests hn hc o).val).val = (number o.val).val := by
  induction requests generalizing N s with
  | nil => rfl
  | cons i is ih =>
    change (equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (Boundary.carryRequests (s.cross a i height (hc i (by simp))) a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
        (Boundary.transport s a i height (hc i (by simp)) o)).val).val = _
    rw [ih]
    exact Numbering.finEquiv_survivor s number a i height (hc i (by simp))
      o.val (fun k hk => o.property ⟨k,hk⟩)

theorem current_xor_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height : Nat) (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ i ∈ requests, s.Covered i height) (j : Fin 8) :
    (equiv s number a height requests hn hc
      ((s.crossRequests a height requests hn hc).positioned.registry.xors.embed a j)).val =
      (number (s.positioned.registry.xors.embed a j)).val := by
  induction requests generalizing N s with
  | nil => rfl
  | cons i is ih =>
    change (equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (((s.cross a i height (hc i (by simp))).crossRequests a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)).positioned.registry.xors.embed a j)).val = _
    rw [ih]
    exact Numbering.finEquiv_current_xor s number a i height (hc i (by simp)) j

theorem other_xor_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a b : Fin n) (hba : b ≠a) (height : Nat) (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ i ∈ requests, s.Covered i height) (j : Fin 8) :
    (equiv s number a height requests hn hc
      ((s.crossRequests a height requests hn hc).positioned.registry.xors.embed b j)).val =
      (number (s.positioned.registry.xors.embed b j)).val := by
  induction requests generalizing N s with
  | nil => rfl
  | cons i is ih =>
    change (equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (((s.cross a i height (hc i (by simp))).crossRequests a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)).positioned.registry.xors.embed b j)).val = _
    rw [ih]
    change (finSumFinEquiv ((Equiv.sumCongr number Numbering.retainedEquiv)
      (Numbering.equiv s a i height (hc i (by simp)) _))).val = _
    rw [Numbering.equiv_other_xor _ _ _ _ _ _ hba]
    rfl

/-- A newly allocated vertex is outside the refreshed current XOR, so every
remaining request transports it without changing its fresh name. -/
def freshOutside {n : Nat} (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : SatCrossingHorizontal.RetainedVertex) :
    Boundary.Outside (s.cross a line height hc) a :=
  ⟨.inr v.val, by
    rintro ⟨j,hj⟩
    rw [Horizontal.latest_active] at hj
    exact SatCrossingHorizontal.retained_ne_zero v j (Sum.inr.inj hj)⟩

theorem first_fresh_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height i : Nat) (is : List Nat) (hn : (i::is).Nodup)
    (hc : ∀ j ∈ i::is, s.Covered j height) (v : SatCrossingHorizontal.RetainedVertex) :
    (equiv s number a height (i::is) hn hc
      (Boundary.carryRequests (s.cross a i height (hc i (by simp))) a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
        (freshOutside s a i height (hc i (by simp)) v)).val).val =
      N+(Numbering.retainedIndex v).val := by
  change (equiv (s.cross a i height (hc i (by simp)))
    (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
    (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
    (Boundary.carryRequests (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (freshOutside s a i height (hc i (by simp)) v)).val).val = _
  rw [carried_names]
  exact Numbering.finEquiv_retained s number a i height (hc i (by simp)) v

/-- Retiring the active XOR changes only registry labels, so this is also
the numbering of the complete next insertion state. -/
noncomputable def nextEquiv {n N : Nat} (s : IntervalState (n +1))
    (number : s.Vertex ≃ Fin N) (height : Nat → Nat) (j : Nat) (h : Ready s height j) :
    (next s height j h).Vertex ≃ Fin (N+40*(requests height j).length) :=
  equiv s number 0 (height j) (requests height j) (requests_nodup height j)
    h.requests_covered

end GridHardness.CorrectedSatInterval.RowNumbering
