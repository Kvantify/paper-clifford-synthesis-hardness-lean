/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleCardinalSegments

/-!
# Signed Tentacle Drawing From

Cardinal strip compilation from an arbitrary signed initial frame,
phase and lane. This permits the initial rung to be a prescribed cluster
dock while the ideal centerline follows its other lane exactly.
-/

@[expose] public section

namespace GridHardness.SignedTentacle.CardinalRunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def drawingFrom (s : RunState) (length : Nat) (rs : List Run) : Drawing :=
  RunChain.compile s length (requests s length rs)

theorem drawingFrom_start (s : RunState) (length : Nat) (rs : List Run) (r : Fin 2) :
    (drawingFrom s length rs).start r = near s.frame r :=
  RunChain.compile_start _ _ _ _

theorem drawingFrom_ideal_start (s : RunState) (length : Nat) (rs : List Run)
    (hs : s.phase = 0) : (drawingFrom s length rs).start s.lane = s.point 0 :=
  RunChain.compile_ideal_start _ _ _ hs

theorem drawingFrom_terminal (s : RunState) (length : Nat) (rs : List Run) :
    (drawingFrom s length rs).lastFrame =
        (RunChain.terminal s length (requests s length rs)).1.frame ∧
      (drawingFrom s length rs).lastLength =
        (RunChain.terminal s length (requests s length rs)).1.length
          (RunChain.terminal s length (requests s length rs)).2 :=
  RunChain.compile_terminal _ _ _

theorem drawingFrom_tip (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection, length)::rs)).getLast? =
      some ((drawingFrom s length rs).tip
        (RunChain.terminal s length (requests s length rs)).1.lane) := by
  rw [← idealRoute_requests s length rs hc, idealRoute_last]
  rw [drawingFrom, RunChain.compile_ideal_tip]

theorem drawingFrom_segments (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    (RunChain.runs s length (requests s length rs)).map toCardinal =
      LatticeRouteRuns.segments (s.point 0) ((s.frame.axisDirection, length)::rs) :=
  requests_segments s length rs hc

theorem drawingFrom_mem (s : RunState) (length : Nat) (rs : List Run) (p : Point) :
    p ∈ (drawingFrom s length rs).points ↔
      ∃ a ∈ RunChain.runs s length (requests s length rs), p ∈ RunChain.segmentStrip a :=
  RunChain.compile_mem _ _ _ _

theorem drawingFrom_mem_index (s : RunState) (length : Nat) (rs : List Run) (p : Point) :
    p ∈ (drawingFrom s length rs).points ↔
      ∃ (i : Nat), ∃ (hi : i < (RunChain.runs s length (requests s length rs)).length),
        p ∈ RunChain.segmentStrip ((RunChain.runs s length (requests s length rs))[i]'hi) := by
  rw [drawingFrom_mem]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ⟨i, hi, hp⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨_, List.getElem_mem hi, hp⟩

/-- The entire initial dock strip is retained by the compiler. -/
theorem drawingFrom_firstStrip_mem (s : RunState) (length : Nat) (rs : List Run)
    (p : Point) (hp : p ∈ strip s.frame (s.length length)) :
    p ∈ (drawingFrom s length rs).points := by
  apply (drawingFrom_mem s length rs p).mpr
  refine ⟨(s, length), ?_, hp⟩
  rw [RunChain.runs_self_tail]
  exact List.mem_cons_self

/-- The entire final strip is retained, including its terminal rung. -/
theorem drawingFrom_lastStrip_mem (s : RunState) (length : Nat) (rs : List Run)
    (p : Point)
    (hp : p ∈ strip (drawingFrom s length rs).lastFrame (drawingFrom s length rs).lastLength) :
    p ∈ (drawingFrom s length rs).points := by
  rw [Drawing.points_prefix]
  exact Finset.mem_union_right _ hp

theorem drawingFrom_ideal_tip (s : RunState) (length : Nat) (rs : List Run) :
    (drawingFrom s length rs).tip
        (RunChain.terminal s length (requests s length rs)).1.lane =
      (RunChain.terminal s length (requests s length rs)).1.point
        (RunChain.terminal s length (requests s length rs)).2 :=
  RunChain.compile_ideal_tip _ _ _

theorem drawingFrom_stripCount (s : RunState) (length : Nat) (rs : List Run) :
    RunChain.stripCount (drawingFrom s length rs) = rs.length + 1 := by
  rw [drawingFrom, RunChain.compile_stripCount, requests_length]

theorem drawingFrom_halfSize_le (s : RunState) (length : Nat) (rs : List Run) :
    (drawingFrom s length rs).halfSize ≤
      1 + (length + (rs.map Prod.snd).sum) + (rs.length + 1) := by
  have h := RunChain.compile_halfSize_le s length (requests s length rs)
  simpa only [drawingFrom, RunChain.idealLength, requests_length, requests_lengths] using h

theorem drawingFrom_valid (s : RunState) (length : Nat) (rs : List Run)
    (hl : 3 ≤ length) (hn : ∀ r ∈ rs, 3 ≤ r.2)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2))
    (hclear : CardinalClearance (LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection, length)::rs))) : (drawingFrom s length rs).Valid := by
  apply RunChain.compile_valid_of_segment_distance _ _ _ hl (requests_lower _ _ _ 3 hn)
  apply indexedClearance_of_cardinal
  rwa [requests_segments s length rs hc]

theorem segment_point_mem_expand (p : Point) (rs : List Run)
    (a : LatticeRouteRuns.Segment) (ha : a ∈ LatticeRouteRuns.segments p rs)
    (k : Nat) (hk : k ≤ a.2.2) :
    LatticeRouteRuns.segmentPoint a k ∈ LatticeRouteRuns.expandRuns p rs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < rs.length := by simpa only [LatticeRouteRuns.segments_length] using hi
  rw [LatticeRouteRuns.segments_getElem_run p rs i hi'] at hk
  rw [LatticeRouteRuns.segmentPoint_getElem p rs i k hi' hk]
  exact List.getElem_mem _

/-- Uniform two-unit containment also holds for a prescribed initial
frame, phase and lane. -/
theorem drawingFrom_centerline_distance (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2))
    (q : Point) (hq : q ∈ (drawingFrom s length rs).points) :
    ∃ r ∈ LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection, length)::rs),
      IntegerGrid.manhattan q r ≤ 2 := by
  obtain ⟨a, ha, k, hk0, hka, hdist⟩ := RunChain.compile_centerline_distance
    s length (requests s length rs) q hq
  have ham : toCardinal a ∈
      LatticeRouteRuns.segments (s.point 0) ((s.frame.axisDirection, length)::rs) := by
    rw [← requests_segments s length rs hc]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hk : k.toNat ≤ (toCardinal a).2.2 := Int.toNat_le.mpr hka
  have hmem := segment_point_mem_expand (s.point 0) ((s.frame.axisDirection, length)::rs)
    (toCardinal a) ham k.toNat hk
  rw [toCardinal_point, Int.toNat_of_nonneg hk0] at hmem
  exact ⟨a.1.point k, hmem, hdist⟩

end GridHardness.SignedTentacle.CardinalRunChain
