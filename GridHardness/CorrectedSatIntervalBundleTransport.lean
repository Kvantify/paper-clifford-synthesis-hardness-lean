/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetainedEdges

/-!
# Corrected SAT Interval Bundle Transport

Registered residual intervals carry actual mandatory arcs. If no later
request enters an interval, its four arcs survive with exactly their old
vertex names. The hypothesis concerns numerical cut positions only.
-/

public section

namespace GridHardness.CorrectedSatInterval.BundleTransport
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : Nat}

theorem cross_endpoint (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (b : s.BundleId)
    (hb : b ≠(s.select line height hc).val) (p : Slot) :
    endpoint ((s.cross a line height hc).positioned.registry.bundles (.inl ⟨b,hb⟩)) p =
      crossLift s a line height hc (endpoint (s.positioned.registry.bundles b) p) := by
  let o : Boundary.Outside s a := ⟨endpoint (s.positioned.registry.bundles b) p,by
    rintro ⟨v,hv⟩
    exact s.positioned.registry.disjoint a b v p hv⟩
  rw [show endpoint ((s.cross a line height hc).positioned.registry.bundles (.inl ⟨b,hb⟩)) p =
      endpoint (s.positioned.registry.crossBundle a (s.select line height hc).val b) p from rfl,
    s.positioned.registry.crossBundle_other a (s.select line height hc).val b hb]
  exact (crossLift_survivor s a line height hc o).symm

theorem row (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (b : s.BundleId) (hb : ∀ i ∈rs, ¬(s.positioned.segments b).Contains i height) :
    ∃ c : (s.crossRequests a height rs hn hc).BundleId,
      (s.crossRequests a height rs hn hc).positioned.segments c=s.positioned.segments b ∧
      ∀ p, endpoint ((s.crossRequests a height rs hn hc).positioned.registry.bundles c) p=
        rowLift s a height rs hn hc (endpoint (s.positioned.registry.bundles b) p) := by
  induction rs generalizing s with
  | nil => exact ⟨b,rfl,fun _ => rfl⟩
  | cons i is ih =>
    have hne : b≠(s.select i height (hc i (by simp))).val := by
      intro he
      exact hb i (by simp) (he ▸ (s.select i height (hc i (by simp))).property)
    let c : (s.cross a i height (hc i (by simp))).BundleId := .inl ⟨b,hne⟩
    obtain ⟨d,hd,he⟩ := ih (s.cross a i height (hc i (by simp)))
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc) c
      (fun k hk => hb k (by simp [hk]))
    refine ⟨d,hd,?_⟩
    intro p
    exact (he p).trans (congrArg
      (rowLift (s.cross a i height _) a height is _ _)
      (cross_endpoint s a i height _ b hne p))

/-- Survival of an actual bundle through the remainder of the sweep. -/
theorem run (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (b : s.BundleId),
      (∀ k, j≤k → k<j+n →
        ¬(s.positioned.segments b).Contains (s.positioned.segments b).line (height k)) →
      ∃ c : (runState height hinj hpos n j s h).BundleId,
        (runState height hinj hpos n j s h).positioned.segments c=s.positioned.segments b ∧
        ∀ p, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c) p=
          runLift height hinj hpos n j s h (endpoint (s.positioned.registry.bundles b) p) := by
  induction n with
  | zero => intro j s h b hb; exact ⟨b,rfl,fun _ => rfl⟩
  | succ n ih =>
    intro j s h b hb
    obtain ⟨c,hc,he⟩ := row s 0 (height j) (requests height j) (requests_nodup height j)
      h.requests_covered b (by
        intro i hi hbi
        exact hb j le_rfl (by omega) ⟨rfl,hbi.2⟩)
    change (crossed s height j h).positioned.segments c=s.positioned.segments b at hc
    change ∀ p, endpoint ((crossed s height j h).positioned.registry.bundles c) p=
      nextLift s height j h (endpoint (s.positioned.registry.bundles b) p) at he
    obtain ⟨d,hd,hf⟩ := ih (j+1) (next s height j h)
      (next_ready s height hinj hpos j h) (some c) (by
        intro k hk hkn
        change ¬((crossed s height j h).positioned.segments c).Contains
          ((crossed s height j h).positioned.segments c).line (height k)
        rw [hc]
        exact hb k (by omega) (by omega))
    refine ⟨d,hd.trans hc,?_⟩
    intro p
    exact (hf p).trans (congrArg
      (runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)) (he p))

/-- The surviving endpoints form an actual final graph arc, not merely a
geometric continuation. -/
theorem run_edge (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n j : Nat) (s : IntervalState n) (h : Ready s height j)
    (b : s.BundleId)
    (hb : ∀ k, j ≤k → k <j+n →
      ¬(s.positioned.segments b).Contains (s.positioned.segments b).line (height k))
    (r : Fin 4) :
    (runState height hinj hpos n j s h).adj
      (runLift height hinj hpos n j s h ((s.positioned.registry.bundles b).source r))
      (runLift height hinj hpos n j s h ((s.positioned.registry.bundles b).target r)) := by
  obtain ⟨c,_,he⟩ := run height hinj hpos n j s h b hb
  have hh := ((runState height hinj hpos n j s h).positioned.registry.bundles c).edge r
  change (runState height hinj hpos n j s h).adj
    (endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c) (r,false))
    (endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c) (r,true)) at hh
  simpa only [he,endpoint_false,endpoint_true] using hh

/-- The outgoing adjacency of each surviving mandatory source is exact:
no unlisted edge can leave it in the final graph. -/
theorem run_outgoing_iff (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n j : Nat) (s : IntervalState n) (h : Ready s height j)
    (b : s.BundleId)
    (hb : ∀ k, j ≤k → k <j+n →
      ¬(s.positioned.segments b).Contains (s.positioned.segments b).line (height k))
    (r : Fin 4) (v : (runState height hinj hpos n j s h).Vertex) :
    (runState height hinj hpos n j s h).adj
      (runLift height hinj hpos n j s h ((s.positioned.registry.bundles b).source r)) v ↔
      v=runLift height hinj hpos n j s h ((s.positioned.registry.bundles b).target r) := by
  obtain ⟨c,_,he⟩ := run height hinj hpos n j s h b hb
  have hs := he (r,false)
  have ht := he (r,true)
  simp only [endpoint_false,endpoint_true] at hs ht
  rw [←hs,←ht]
  exact ⟨fun hadj => ((runState height hinj hpos n j s h).positioned.registry.bundles c).unique r v hadj,
    fun hv => hv ▸ ((runState height hinj hpos n j s h).positioned.registry.bundles c).edge r⟩

end GridHardness.CorrectedSatInterval.BundleTransport
