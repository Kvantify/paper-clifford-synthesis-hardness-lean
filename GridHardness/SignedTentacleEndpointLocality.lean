/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleCardinalSegments
public import GridHardness.LatticeRouteRunEndpoints

/-!
# Signed Tentacle Endpoint Locality

Points near either endpoint of a compiled strip chain belong to its
first or last strip. The conclusion follows from quantitative route-index
separation and the minimum length of the computed runs.
-/

public section

namespace GridHardness.SignedTentacle.CardinalRunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every noninitial generated ideal segment is far from the exact start. -/
theorem requests_start_distance (s : RunState) (length : Nat) (rs : List Run)
    (scale lower : Nat)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection,length)::rs)))
    (hn : ∀ r ∈(s.frame.axisDirection,length)::rs, lower ≤ r.2)
    (i : Nat) (hi : i < (RunChain.runs s length (requests s length rs)).length) (hi0 : 0 < i)
    (k : Int) (hk0 : 0 ≤ k)
    (hk : k ≤ ((RunChain.runs s length (requests s length rs))[i]'hi).2) :
    min scale lower≤IntegerGrid.manhattan (s.point 0)
      (((RunChain.runs s length (requests s length rs))[i]'hi).1.point k) := by
  have hmap := requests_segments s length rs hc
  have hci : i<(LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection,length)::rs)).length := by
    rw [← hmap,List.length_map]
    exact hi
  have hck : k.toNat≤((LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection,length)::rs))[i]'hci).2.2 := by
    simp only [← hmap,List.getElem_map,toCardinal]
    exact Int.toNat_le.mpr hk
  have h := LatticeRouteRuns.segment_start_distance scale lower (s.point 0)
    ((s.frame.axisDirection,length)::rs) hs hn i hci hi0 k.toNat hck
  simpa only [← hmap,List.getElem_map,toCardinal_point,Int.toNat_of_nonneg hk0] using h

/-- Every nonterminal generated ideal segment is far from the exact end. -/
theorem requests_end_distance (s : RunState) (length : Nat) (rs : List Run)
    (scale lower : Nat)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection,length)::rs)))
    (hn : ∀ r ∈(s.frame.axisDirection,length)::rs, lower ≤ r.2)
    (i : Nat) (hi : i < (RunChain.runs s length (requests s length rs)).length)
    (hi1 : i + 1<(RunChain.runs s length (requests s length rs)).length)
    (k : Int) (hk0 : 0 ≤ k)
    (hk : k ≤ ((RunChain.runs s length (requests s length rs))[i]'hi).2) :
    min scale lower≤IntegerGrid.manhattan
      (((RunChain.runs s length (requests s length rs))[i]'hi).1.point k)
      (LatticeRouteRuns.runEnd (s.point 0) ((s.frame.axisDirection,length)::rs)) := by
  have hmap := requests_segments s length rs hc
  have hci : i<(LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection,length)::rs)).length := by
    rw [← hmap,List.length_map]
    exact hi
  have hci1 : i+1<(LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection,length)::rs)).length := by
    rw [← hmap,List.length_map]
    exact hi1
  have hck : k.toNat≤((LatticeRouteRuns.segments (s.point 0)
      ((s.frame.axisDirection,length)::rs))[i]'hci).2.2 := by
    simp only [← hmap,List.getElem_map,toCardinal]
    exact Int.toNat_le.mpr hk
  have h := LatticeRouteRuns.segment_end_distance scale lower (s.point 0)
    ((s.frame.axisDirection,length)::rs) hs hn i hci hci1 k.toNat hck
  simpa only [← hmap,List.getElem_map,toCardinal_point,Int.toNat_of_nonneg hk0] using h

/-- Any compiled point closer than the run-separation margin, allowing
for the strip's two-unit width, belongs to the initial strip. -/
theorem compile_first_strip_of_close (s : RunState) (length : Nat) (rs : List Run)
    (scale lower : Nat)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection,length)::rs)))
    (hn : ∀ r ∈(s.frame.axisDirection,length)::rs, lower ≤ r.2)
    (q : Point) (hq : q ∈ (RunChain.compile s length (requests s length rs)).points)
    (hclose : IntegerGrid.manhattan (s.point 0) q + 2<min scale lower) :
    q∈strip s.frame (s.length length) := by
  obtain ⟨a,ha,hqa⟩ := (RunChain.compile_mem s length (requests s length rs) q).mp hq
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  by_cases hi0 : i=0
  · subst i
    have hh := RunChain.runs_head s length (requests s length rs)
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem hi] at hh
    have he := Option.some.inj hh
    simpa only [he,RunChain.segmentStrip] using hqa
  · obtain ⟨k,hk0,hka,hkq⟩ :=
      ((RunChain.runs s length (requests s length rs))[i]'hi).1.strip_distance
        ((RunChain.runs s length (requests s length rs))[i]'hi).2 q hqa
    have hd := requests_start_distance s length rs scale lower hc hs hn i hi (by omega)
      k hk0 hka
    have ht := IntegerGrid.manhattan_triangle (s.point 0) q
      (((RunChain.runs s length (requests s length rs))[i]'hi).1.point k)
    omega

/-- The terminal analogue identifies the actual final strip, retaining
its phase-corrected frame and length. -/
theorem compile_last_strip_of_close (s : RunState) (length : Nat) (rs : List Run)
    (scale lower : Nat)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection,length)::rs)))
    (hn : ∀ r ∈(s.frame.axisDirection,length)::rs, lower ≤ r.2)
    (q : Point) (hq : q ∈ (RunChain.compile s length (requests s length rs)).points)
    (hclose : IntegerGrid.manhattan q
      (LatticeRouteRuns.runEnd (s.point 0) ((s.frame.axisDirection,length)::rs)) + 2<min scale lower) :
    q∈strip (RunChain.compile s length (requests s length rs)).lastFrame
      (RunChain.compile s length (requests s length rs)).lastLength := by
  obtain ⟨a,ha,hqa⟩ := (RunChain.compile_mem s length (requests s length rs) q).mp hq
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  by_cases hi1 : i+1=(RunChain.runs s length (requests s length rs)).length
  · have hh := RunChain.runs_last s length (requests s length rs)
    rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at hh
    have he : (RunChain.runs s length (requests s length rs))[i]'hi=
        RunChain.terminal s length (requests s length rs) := by
      have hind : (RunChain.runs s length (requests s length rs)).length-1=i := by omega
      simpa only [hind,Option.some.injEq] using hh
    have hterminal := RunChain.compile_terminal s length (requests s length rs)
    simpa only [hterminal.1,hterminal.2,he,RunChain.segmentStrip] using hqa
  · obtain ⟨k,hk0,hka,hkq⟩ :=
      ((RunChain.runs s length (requests s length rs))[i]'hi).1.strip_distance
        ((RunChain.runs s length (requests s length rs))[i]'hi).2 q hqa
    have hd := requests_end_distance s length rs scale lower hc hs hn i hi (by omega)
      k hk0 hka
    have ht := IntegerGrid.manhattan_triangle
      (((RunChain.runs s length (requests s length rs))[i]'hi).1.point k) q
      (LatticeRouteRuns.runEnd (s.point 0) ((s.frame.axisDirection,length)::rs))
    rw [IntegerGrid.manhattan_comm q] at hkq
    omega

/-- The prescribed phase-zero owner strip has the sharper one-unit
centerline bound. Combined with initial-strip locality this avoids losing
an unnecessary unit in the exact owner-dock clearance estimates. -/
theorem initial_strip_distance_zero (s : RunState) (length : Nat) (hphase : s.phase = 0)
    (q : Point) (hq : q ∈ strip s.frame (s.length length)) :
    ∃ k : Int, 0≤k ∧ k≤length ∧ IntegerGrid.manhattan q (s.point k)≤1 := by
  have hq' : q∈strip s.frame (runLength 0 length) := by
    simpa only [RunState.length,hphase] using hq
  simpa only [RunState.point,hphase] using run_strip_distance_zero s.frame s.lane length q hq'

end GridHardness.SignedTentacle.CardinalRunChain
