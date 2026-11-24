/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalVerticalRun

/-!
# Corrected SAT Interval Vertical Spans

Before either of two consecutive vertical crossings has been processed,
their heights lie in the same registered interval. This spanning invariant
survives every cut outside their closed height interval and supplies the
anchored endpoint invariant when the first crossing is processed.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering HorizontalEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Nat}

def Spans (s : IntervalState n) (line low high : Nat) : Prop :=
  ∃ b : s.BundleId, (s.positioned.segments b).line=line ∧
    (s.positioned.segments b).lower<low ∧ high<(s.positioned.segments b).upper

theorem spans_cross (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hv : Spans s line low high) (cutLine cutHeight : Nat)
    (hc : s.Covered cutLine cutHeight)
    (hcut : cutLine ≠line ∨ cutHeight <low ∨ high <cutHeight) :
    Spans (s.cross a cutLine cutHeight hc) line low high := by
  obtain ⟨b,hline,hlo,hhi⟩ := hv
  by_cases hb : b=(s.select cutLine cutHeight hc).val
  · have hsel := (s.select cutLine cutHeight hc).property
    rw [←hb] at hsel
    have hline' : cutLine=line := hsel.1.symm.trans hline
    have hsep : cutHeight<low ∨ high<cutHeight := hcut.resolve_left (by simp [hline'])
    rcases hsep with hcl | hch
    · refine ⟨.inr false,?_,hcl,?_⟩
      · exact (s.select cutLine cutHeight hc).property.1.trans hline'
      · change high<(s.positioned.segments (s.select cutLine cutHeight hc).val).upper
        simpa only [←hb] using hhi
    · refine ⟨.inr true,?_,?_,hch⟩
      · exact (s.select cutLine cutHeight hc).property.1.trans hline'
      · change (s.positioned.segments (s.select cutLine cutHeight hc).val).lower<low
        simpa only [←hb] using hlo
  · exact ⟨.inl ⟨b,hb⟩,hline,hlo,hhi⟩

theorem spans_row (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hv : Spans s line low high) (height : Nat) (rs : List Nat) (hn : rs.Nodup)
    (hc : ∀ i ∈rs, s.Covered i height)
    (hcut : ∀ i ∈rs, i≠line ∨ height <low ∨ high <height) :
    Spans (s.crossRequests a height rs hn hc) line low high := by
  induction rs generalizing s with
  | nil => exact hv
  | cons i is ih =>
    exact ih (s.cross a i height (hc i (by simp)))
      (spans_cross s a line low high hv i height _ (hcut i (by simp)))
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (fun k hk => hcut k (by simp [hk]))

theorem spans_retire (s : IntervalState (n +1)) (line low high : Nat)
    (hv : Spans s line low high) (newLine upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠newLine) :
    Spans (s.retire newLine upper hfresh) line low high := by
  obtain ⟨b,hb⟩ := hv
  exact ⟨some b,hb⟩

theorem spans_cross_anchored (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hord : low <high) (lower : Bool) (hv : Spans s line low high)
    (hc : s.Covered line (if lower then low else high)) :
    Anchored (s.cross a line (if lower then low else high) hc) line low high lower
      (fun r => .inr (boundaryPort lower r).val) := by
  obtain ⟨b,hline,hlo,hhi⟩ := hv
  have hcontains : (s.positioned.segments b).Contains line (if lower then low else high) := by
    refine ⟨hline,?_,?_⟩ <;> cases lower <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    all_goals omega
  have hb := s.positioned.unique line (if lower then low else high) b
    (s.select line (if lower then low else high) hc).val hcontains
    (s.select line (if lower then low else high) hc).property
  exact cross_anchored s a line low high lower hc (by rw [←hb]; exact ⟨hlo,hhi⟩)

/-- The first selected request installs the anchor with its exact row-fresh
name; the other requests of the row preserve that name. -/
theorem spans_row_anchored (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hord : low <high) (lower : Bool) (hv : Spans s line low high)
    (height : Nat) (hheight : height =(if lower then low else high))
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (ht : rs[t.val] =line) :
    Anchored (s.crossRequests a height rs hn hc) line low high lower
      (fun r => rowFresh s a height rs hn hc t (boundaryPort lower r)) := by
  subst height
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht0 : t.val=0
    · have hiline : i=line := by simpa only [ht0,List.getElem_cons_zero] using ht
      subst i
      simp only [rowFresh,dite_eq_left ht0]
      exact anchored_row _ a line low high lower _
        (spans_cross_anchored s a line low high hord lower hv (hc line (by simp)))
        (if lower then low else high) is (List.nodup_cons.mp hn).2
        (s.cross_remaining_covered a (if lower then low else high) line is hn hc)
        (fun i hi => Or.inl (by intro he; exact (List.nodup_cons.mp hn).1 (he ▸ hi)))
    · have httail : t.val - 1 < is.length := by
        have := t.isLt
        simp only [List.length_cons] at this
        omega
      have htail : is[t.val-1]=line := by
        have hh : (i::is)[t.val-1+1]'(by simpa only [List.length_cons] using Nat.succ_lt_succ httail)=line :=
          by simpa only [show t.val-1+1=t.val by omega] using ht
        simpa only [List.getElem_cons_succ] using hh
      have hne : i≠line := by
        intro he
        have hm : line∈is := htail ▸ List.getElem_mem httail
        exact (List.nodup_cons.mp hn).1 (he.symm ▸ hm)
      simp only [rowFresh,dite_eq_right ht0]
      exact ih (s.cross a i (if lower then low else high) (hc i (by simp)))
        (spans_cross s a line low high hv i (if lower then low else high) _ (Or.inl hne))
        (List.nodup_cons.mp hn).2 ⟨t.val-1,httail⟩
        (s.cross_remaining_covered a (if lower then low else high) i is hn hc) htail

end GridHardness.CorrectedSatInterval.VerticalEdges
