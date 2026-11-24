/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalVerticalAnchors
public import GridHardness.CorrectedSatIntervalHorizontalEdges

/-!
# Corrected SAT Interval Vertical Run

Actual vertical connectors in a complete sweep, from an anchored interval
to the retained ports of a specified later request. All future preservation
hypotheses are numerical conditions on the other crossing heights.
-/

public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering HorizontalEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Nat}

theorem anchored_row_connect (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hord : low <high) (lower : Bool) (v : Fin 4 → s.Vertex)
    (hv : Anchored s line low high lower v)
    (height : Nat) (hheight : height =(if lower then high else low))
    (rs : List Nat) (hn : rs.Nodup)
    (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (ht : rs[t.val] =line) :
    let s' := s.crossRequests a height rs hn hc
    ∃ b : s'.BundleId, s'.positioned.segments b=⟨line,low,high⟩ ∧
      (∀ r, endpoint (s'.positioned.registry.bundles b) (boundarySlot lower r)=
        rowLift s a height rs hn hc (v r)) ∧
      (∀ r, endpoint (s'.positioned.registry.bundles b) (boundarySlot (!lower) r)=
        rowFresh s a height rs hn hc t (boundaryPort (!lower) r)) := by
  subst height
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht0 : t.val=0
    · have hiline : i=line := by simpa only [ht0,List.getElem_cons_zero] using ht
      subst i
      have hconnect := anchored_connect s a line low high hord lower v hv (hc line (by simp))
      obtain ⟨b,hb,he⟩ := BundleTransport.row
        (s.cross a line (if lower then high else low) (hc line (by simp))) a
        (if lower then high else low) is (List.nodup_cons.mp hn).2
        (s.cross_remaining_covered a (if lower then high else low) line is hn hc)
        (.inr lower) (by
          intro i hi hcontains
          rw [hconnect.1] at hcontains
          have hie : line=i := hcontains.1
          exact (List.nodup_cons.mp hn).1 (hie.symm ▸ hi))
      refine ⟨b,hb.trans hconnect.1,?_,?_⟩
      · intro r
        exact (he (boundarySlot lower r)).trans
          (congrArg (rowLift _ a (if lower then high else low) is _ _) (hconnect.2.1 r))
      · intro r
        simp only [rowFresh,dite_eq_left ht0]
        exact (he (boundarySlot (!lower) r)).trans
          (congrArg (rowLift _ a (if lower then high else low) is _ _) (hconnect.2.2 r))
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
      obtain ⟨b,hb,he,hf⟩ := ih (s.cross a i (if lower then high else low) (hc i (by simp)))
        (fun r => crossLift s a i (if lower then high else low) _ (v r))
        (anchored_cross s a line low high lower v hv i (if lower then high else low) _ (Or.inl hne))
        (List.nodup_cons.mp hn).2 ⟨t.val-1,httail⟩
        (s.cross_remaining_covered a (if lower then high else low) i is hn hc)
        htail
      refine ⟨b,hb,he,?_⟩
      intro r
      simp only [rowFresh,dite_eq_right ht0]
      exact hf r

/-- The connector interval and both endpoint maps after the complete run.
The remaining hypotheses merely exclude other cut heights between or at the
two desired heights; no graph adjacency is assumed. -/
theorem anchored_run_connect (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (line low high : Nat) (_hord : low<high) (lower : Bool)
      (v : Fin 4 → s.Vertex) (_hv : Anchored s line low high lower v)
      (a : Fin n) (t : Fin (requests height (j+a.val)).length),
      (requests height (j+a.val))[t.val]=line →
      height (j+a.val)=(if lower then high else low) →
      (∀ k, j≤k → k<j+n → k≠j+a.val → height k<low ∨ high<height k) →
      ∃ b : (runState height hinj hpos n j s h).BundleId,
        (runState height hinj hpos n j s h).positioned.segments b=⟨line,low,high⟩ ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles b)
            (boundarySlot lower r)=runLift height hinj hpos n j s h (v r)) ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles b)
            (boundarySlot (!lower) r)=runFresh height hinj hpos n j s h
              (rowIndex height n j a t) (boundaryPort (!lower) r)) := by
  induction n with
  | zero => intro j s h line low high hord lower v hv a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h line low high hord lower v hv a t ht htgt hgap
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have hhe : height j=(if lower then high else low) := by simpa using htgt
      have hrow : ∃ b : (crossed s height j h).BundleId,
          (crossed s height j h).positioned.segments b=⟨line,low,high⟩ ∧
          (∀ r, endpoint ((crossed s height j h).positioned.registry.bundles b)
            (boundarySlot lower r)=nextLift s height j h (v r)) ∧
          (∀ r, endpoint ((crossed s height j h).positioned.registry.bundles b)
            (boundarySlot (!lower) r)=rowFresh s 0 (height j) (requests height j)
              (requests_nodup height j) h.requests_covered
              ⟨t.val,t.isLt⟩ (boundaryPort (!lower) r)) := by
        have hh := anchored_row_connect s 0 line low high hord lower v hv (height j) hhe
          (requests height j) (requests_nodup height j)
          h.requests_covered
          ⟨t.val,t.isLt⟩ (by simpa using ht)
        exact hh
      obtain ⟨b,hb,he,hf⟩ := hrow
      obtain ⟨c,hc,hg⟩ := BundleTransport.run height hinj hpos n (j+1)
        (next s height j h) (next_ready s height hinj hpos j h) (some b) (by
          intro k hk hkn
          change ¬((crossed s height j h).positioned.segments b).Contains
            ((crossed s height j h).positioned.segments b).line (height k)
          rw [hb]
          intro hh
          have hhh := hh.2
          change low<height k ∧ height k<high at hhh
          have hgk := hgap k (by omega) (by omega) (by simp; omega)
          omega)
      refine ⟨c,hc.trans hb,?_,?_⟩
      · intro r
        exact (hg (boundarySlot lower r)).trans
          (congrArg (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)) (he r))
      · intro r
        simp only [runFresh,rowIndex_zero,show t.val<(requests height j).length from t.isLt,
          ↓reduceDIte]
        exact (hg (boundarySlot (!lower) r)).trans
          (congrArg (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)) (hf r))
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      let t' : Fin (requests height (j+1+b.val)).length :=
        ⟨t.val,by simpa only [hj] using t.isLt⟩
      have hv' : Anchored (next s height j h) line low high lower
          (fun r => nextLift s height j h (v r)) := by
        apply anchored_retire
        exact anchored_row s 0 line low high lower v hv (height j) (requests height j)
          (requests_nodup height j) h.requests_covered
          (fun i _ => Or.inr (hgap j le_rfl (by omega) (by omega)))
      obtain ⟨c,hc,he,hf⟩ := ih (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) line low high hord lower _ hv' b t'
        (by simpa only [hj,t'] using ht) (by simpa only [hj] using htgt)
        (fun k hk hkn hka => hgap k (by omega) (by omega) (by simpa only [←hj] using hka))
      refine ⟨c,hc,he,?_⟩
      intro r
      have hidx := rowIndex_succ height n j a ha t
      have hnidx : ¬(rowIndex height (n+1) j a t).val<(requests height j).length := by omega
      change endpoint ((runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).positioned.registry.bundles c)
          (boundarySlot (!lower) r)=_
      simp only [runFresh,dite_eq_right hnidx]
      rw [hf r]
      congr 1
      apply Fin.ext
      dsimp only [Fin.val_mk,t',b] at *
      omega

end GridHardness.CorrectedSatInterval.VerticalEdges
