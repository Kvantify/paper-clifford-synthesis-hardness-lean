/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleCardinalRuns
public import GridHardness.LatticeRouteRunSegments

/-!
# Signed Tentacle Cardinal Segments

Exact positioned-segment correspondence for the cardinal strip
compiler. This transfers metric clearance of the input runs into validity
of the constructed width-two drawing.
-/

@[expose] public section

namespace GridHardness.SignedTentacle.CardinalRunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Interpret a generated signed segment in cardinal coordinates. -/
def toCardinal (a : RunChain.Segment) : LatticeRouteRuns.Segment :=
  (a.1.point 0, (a.1.frame.axisDirection, a.2))

theorem toCardinal_point (a : RunChain.Segment) (k : Nat) :
    LatticeRouteRuns.segmentPoint (toCardinal a) k = a.1.point k :=
  (a.1.point_advance k).symm

/-- Generated segments have exactly the starts, cardinal directions and
lengths of the input run list, in the same order. -/
theorem requests_segments (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    (RunChain.runs s length (requests s length rs)).map toCardinal =
      LatticeRouteRuns.segments (s.point 0) ((s.frame.axisDirection, length)::rs) := by
  induction rs generalizing s length with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨d, n⟩
    have hd : s.frame.axisDirection.val % 2 ≠ d.val % 2 := by
      have h := hc
      simp only [List.map_cons, List.isChain_cons_cons] at h
      exact h.1
    let t := s.advance length (s.frame.chooseTurn d)
    have ht : t.frame.axisDirection = d := s.advance_direction length d hd
    have hc' : (t.frame.axisDirection::rs.map Prod.fst).IsChain
        (fun d e => d.val % 2 ≠ e.val % 2) := by
      rw [ht]
      exact hc.tail
    change toCardinal (s, length)::
      (RunChain.runs t n (requests t n rs)).map toCardinal = _
    rw [ih t n hc', ht]
    change toCardinal (s, length)::
      LatticeRouteRuns.segments ((s.advance length (s.frame.chooseTurn d)).point 0)
        ((d, n)::rs) = _
    rw [RunState.advance_start, RunState.point_advance]
    rfl

theorem drawing_segments (p : Point) (d : Fin 4) (length : Nat) (rs : List Run)
    (hc : (d::rs.map Prod.fst).IsChain (fun d e => d.val % 2 ≠ e.val % 2)) :
    (RunChain.runs (initialRunState p d) length
      (requests (initialRunState p d) length rs)).map toCardinal =
      LatticeRouteRuns.segments p ((d, length)::rs) := by
  have hd : (initialRunState p d).frame.axisDirection = d := frameAlong_direction p d
  have h := requests_segments (initialRunState p d) length rs (by rw [hd]; exact hc)
  rwa [initialRunState_point_zero, hd] at h

/-- A metric premise stated entirely using the input's canonical
cardinal segments and natural offsets along their finite lengths. -/
def CardinalClearance (ss : List LatticeRouteRuns.Segment) : Prop :=
  ∀ i j (hi : i < ss.length) (hj : j < ss.length), i + 1 < j →
    ∀ k : Nat, k ≤ (ss[i]'hi).2.2 → ∀ l : Nat, l ≤ (ss[j]'hj).2.2 →
      6 ≤ IntegerGrid.manhattan (LatticeRouteRuns.segmentPoint (ss[i]'hi) k)
        (LatticeRouteRuns.segmentPoint (ss[j]'hj) l)

theorem indexedClearance_of_cardinal (ss : List RunChain.Segment)
    (h : CardinalClearance (ss.map toCardinal)) : RunChain.IndexedClearance ss := by
  intro i j hi hj hij k hk0 hki l hl0 hlj
  have hh := h i j (by simpa using hi) (by simpa using hj) hij k.toNat
    (by simpa only [List.getElem_map, toCardinal] using (Int.toNat_le.mpr hki))
    l.toNat (by simpa only [List.getElem_map, toCardinal] using (Int.toNat_le.mpr hlj))
  simp only [List.getElem_map, toCardinal_point] at hh
  simpa only [Int.toNat_of_nonneg hk0, Int.toNat_of_nonneg hl0] using hh

/-- Actual generated drawing validity from perpendicular cardinal runs,
minimum run lengths and metric clearance of the input's own segments. -/
theorem drawing_valid_of_cardinal_clearance (p : Point) (d : Fin 4) (length : Nat)
    (rs : List Run) (hl : 3 ≤ length) (hn : ∀ r ∈ rs, 3 ≤ r.2)
    (hc : (d::rs.map Prod.fst).IsChain (fun d e => d.val % 2 ≠ e.val % 2))
    (hclear : CardinalClearance (LatticeRouteRuns.segments p ((d, length)::rs))) :
    (drawing p d length rs).Valid := by
  apply drawing_valid p d length rs hl hn
  apply indexedClearance_of_cardinal
  rwa [drawing_segments p d length rs hc]

private theorem cardinal_segment_point_mem (p : Point) (rs : List Run)
    (a : LatticeRouteRuns.Segment) (ha : a ∈ LatticeRouteRuns.segments p rs)
    (k : Nat) (hk : k ≤ a.2.2) :
    LatticeRouteRuns.segmentPoint a k ∈ LatticeRouteRuns.expandRuns p rs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < rs.length := by simpa only [LatticeRouteRuns.segments_length] using hi
  rw [LatticeRouteRuns.segments_getElem_run p rs i hi'] at hk
  rw [LatticeRouteRuns.segmentPoint_getElem p rs i k hi' hk]
  exact List.getElem_mem _

/-- Every point of the actual compiled strip drawing lies within distance
two of a point of the original expanded cardinal route. No validity or
separation premise is needed for this containment theorem. -/
theorem drawing_centerline_distance (p : Point) (d : Fin 4) (length : Nat)
    (rs : List Run)
    (hc : (d::rs.map Prod.fst).IsChain (fun d e => d.val % 2 ≠ e.val % 2))
    (q : Point) (hq : q ∈ (drawing p d length rs).points) :
    ∃ r ∈ LatticeRouteRuns.expandRuns p ((d, length)::rs),
      IntegerGrid.manhattan q r ≤ 2 := by
  obtain ⟨a, ha, k, hk0, hka, hdist⟩ := RunChain.compile_centerline_distance
    (initialRunState p d) length (requests (initialRunState p d) length rs) q hq
  have ham : toCardinal a ∈ LatticeRouteRuns.segments p ((d, length)::rs) := by
    rw [← drawing_segments p d length rs hc]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hk : k.toNat ≤ (toCardinal a).2.2 := Int.toNat_le.mpr hka
  have hmem := cardinal_segment_point_mem p ((d, length)::rs) (toCardinal a) ham k.toNat hk
  rw [toCardinal_point, Int.toNat_of_nonneg hk0] at hmem
  exact ⟨a.1.point k, hmem, hdist⟩

end GridHardness.SignedTentacle.CardinalRunChain
