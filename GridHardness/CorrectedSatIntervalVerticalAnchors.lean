/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalVerticalEdges
public import GridHardness.CorrectedSatIntervalBundleTransport

/-!
# Corrected SAT Interval Vertical Anchors

Tracking an already inserted crossing along a registered vertical
interval. Cuts beyond the other desired crossing may shorten the interval;
they preserve its anchored endpoint exactly. Cutting at the other desired
height then creates the four actual connector arcs.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : Nat}

/-- An endpoint of an interval is fixed at one desired crossing height, and
the other desired height is strictly inside that interval. The endpoint map
records all four directed lanes at once. -/
def Anchored (s : IntervalState n) (line low high : Nat) (lower : Bool)
    (v : Fin 4 → s.Vertex) : Prop :=
  ∃ b : s.BundleId,
    (s.positioned.segments b).line=line ∧
    (if lower then (s.positioned.segments b).lower=low ∧ high<(s.positioned.segments b).upper
      else (s.positioned.segments b).upper=high ∧ (s.positioned.segments b).lower<low) ∧
    ∀ r, endpoint (s.positioned.registry.bundles b) (boundarySlot lower r)=v r

/-- At the first of two desired heights, the continuation towards the other
height is anchored at the newly allocated retained crossing ports. -/
theorem cross_anchored (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (lower : Bool)
    (hc : s.Covered line (if lower then low else high))
    (hspan : (s.positioned.segments (s.select line (if lower then low else high) hc).val).lower <low ∧
      high <(s.positioned.segments (s.select line (if lower then low else high) hc).val).upper) :
    Anchored (s.cross a line (if lower then low else high) hc) line low high lower
      (fun r => .inr (boundaryPort lower r).val) := by
  refine ⟨.inr (!lower),?_,?_,?_⟩
  · cases lower <;> exact (s.select line _ hc).property.1
  · cases lower
    · exact ⟨rfl,hspan.1⟩
    · exact ⟨rfl,hspan.2⟩
  · intro r
    simpa using split_inner_endpoint s a line (if lower then low else high) hc (!lower) r

/-- Intervening cuts on another line, or outside the closed interval between
the desired heights, preserve the anchor. This allows a cut to shorten the
far end of the same bundle; it need not leave the whole bundle unchanged. -/
theorem anchored_cross (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (lower : Bool) (v : Fin 4 → s.Vertex) (hv : Anchored s line low high lower v)
    (cutLine cutHeight : Nat) (hc : s.Covered cutLine cutHeight)
    (hcut : cutLine ≠line ∨ cutHeight <low ∨ high <cutHeight) :
    Anchored (s.cross a cutLine cutHeight hc) line low high lower
      (fun r => crossLift s a cutLine cutHeight hc (v r)) := by
  obtain ⟨b,hline,hbound,hend⟩ := hv
  by_cases hb : b=(s.select cutLine cutHeight hc).val
  · have hsel := (s.select cutLine cutHeight hc).property
    rw [←hb] at hsel
    have hline' : cutLine=line := hsel.1.symm.trans hline
    have hsep : cutHeight<low ∨ high<cutHeight := hcut.resolve_left (by simp [hline'])
    have hinside := hsel.2
    refine ⟨.inr lower,?_,?_,?_⟩
    · cases lower <;> exact (s.select cutLine cutHeight hc).property.1.trans hline'
    · cases lower
      · change (s.positioned.segments (s.select cutLine cutHeight hc).val).upper=high ∧ cutHeight<low
        rw [←hb]
        simp only [Bool.false_eq_true,ite_false] at hbound
        exact ⟨hbound.1,by omega⟩
      · change (s.positioned.segments (s.select cutLine cutHeight hc).val).lower=low ∧ high<cutHeight
        rw [←hb]
        simp only [ite_true] at hbound
        exact ⟨hbound.1,by omega⟩
    · intro r
      rw [split_outer_endpoint,←hb,hend]
  · refine ⟨.inl ⟨b,hb⟩,hline,hbound,?_⟩
    intro r
    rw [BundleTransport.cross_endpoint,hend]

/-- The endpoint invariant is preserved through an entire row of intervening
cuts, including other cuts on the anchored interval's line. -/
theorem anchored_row (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (lower : Bool) (v : Fin 4 → s.Vertex) (hv : Anchored s line low high lower v)
    (height : Nat) (rs : List Nat) (hn : rs.Nodup)
    (hc : ∀ i ∈rs, s.Covered i height)
    (hcut : ∀ i ∈rs, i≠line ∨ height <low ∨ high <height) :
    Anchored (s.crossRequests a height rs hn hc) line low high lower
      (fun r => rowLift s a height rs hn hc (v r)) := by
  induction rs generalizing s with
  | nil => exact hv
  | cons i is ih =>
    exact ih (s.cross a i height (hc i (by simp)))
      (fun r => crossLift s a i height _ (v r))
      (anchored_cross s a line low high lower v hv i height _ (hcut i (by simp)))
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (fun k hk => hcut k (by simp [hk]))

theorem anchored_retire (s : IntervalState (n +1)) (line low high : Nat)
    (lower : Bool) (v : Fin 4 → s.Vertex) (hv : Anchored s line low high lower v)
    (newLine upper : Nat) (hfresh : ∀ b, (s.positioned.segments b).line ≠newLine) :
    Anchored (s.retire newLine upper hfresh) line low high lower v := by
  obtain ⟨b,hb⟩ := hv
  exact ⟨some b,hb⟩

/-- At the second desired height, the interval between the two crossings is
registered with its exact numerical bounds and both exact endpoint maps. -/
theorem anchored_connect (s : IntervalState n) (a : Fin n) (line low high : Nat)
    (hord : low <high) (lower : Bool) (v : Fin 4 → s.Vertex)
    (hv : Anchored s line low high lower v)
    (hc : s.Covered line (if lower then high else low)) :
    let s' := s.cross a line (if lower then high else low) hc
    (s'.positioned.segments (.inr lower)=⟨line,low,high⟩) ∧
    (∀ r, endpoint (s'.positioned.registry.bundles (.inr lower)) (boundarySlot lower r)=
      crossLift s a line (if lower then high else low) hc (v r)) ∧
    (∀ r, endpoint (s'.positioned.registry.bundles (.inr lower)) (boundarySlot (!lower) r)=
      .inr (boundaryPort (!lower) r).val) := by
  obtain ⟨b,hline,hbound,hend⟩ := hv
  have hcontains : (s.positioned.segments b).Contains line (if lower then high else low) := by
    cases lower
    · exact ⟨hline,hbound.2,by simpa [hbound.1] using hord⟩
    · exact ⟨hline,by simpa [hbound.1] using hord,hbound.2⟩
  have hb := s.positioned.unique line (if lower then high else low) b
    (s.select line (if lower then high else low) hc).val hcontains
    (s.select line (if lower then high else low) hc).property
  refine ⟨?_,?_,?_⟩
  · cases lower
    · change (⟨(s.positioned.segments _).line,low,(s.positioned.segments _).upper⟩ : Interval)=_
      rw [←hb,hline,hbound.1]
    · change (⟨(s.positioned.segments _).line,(s.positioned.segments _).lower,high⟩ : Interval)=_
      rw [←hb,hline,hbound.1]
  · intro r
    rw [split_outer_endpoint,←hb,hend]
  · exact fun r => split_inner_endpoint s a line (if lower then high else low) hc lower r

end GridHardness.CorrectedSatInterval.VerticalEdges
