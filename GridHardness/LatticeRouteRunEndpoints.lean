/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunSegments

/-!
# Lattice Route Run Endpoints

Endpoint localization for positioned straight runs. Index separation
and one full intervening run keep every noninitial segment far from the
start, and every nonterminal segment far from the end.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRuns
open CliffordSynthesis LatticeRouteDirections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The exact final point of an expanded run list. -/
def runEnd (p : Point) (rs : List Run) : Point := finish p (expandDirections rs)

theorem expandRuns_getLast (p : Point) (rs : List Run) :
    (expandRuns p rs).getLast?=some (runEnd p rs) := by
  rw [← expand_eq_runs,expand,walk_getLast]
  rfl

theorem expandRuns_first (p : Point) (rs : List Run) :
    (expandRuns p rs)[0]'(by rw [expandRuns_length]; omega)=p := by
  have h (ds : List (Fin 4)) : (walk p ds)[0]'(by simp)=p := by
    cases ds <;> rfl
  simpa only [← expand_eq_runs,expand] using h (expandDirections rs)

theorem expandRuns_last (p : Point) (rs : List Run) :
    (expandRuns p rs)[(rs.map Prod.snd).sum]'(by rw [expandRuns_length]; omega)=runEnd p rs := by
  have h := expandRuns_getLast p rs
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by rw [expandRuns_length]; omega)] at h
  have hlen : (expandRuns p rs).length-1=(rs.map Prod.snd).sum := by rw [expandRuns_length]; omega
  simpa only [hlen,Option.some.injEq] using h

theorem segment_start_index_gap (rs : List Run) (n : Nat) (hn : ∀ r ∈ rs, n ≤r.2)
    (i k : Nat) (hi : i < rs.length) (hi0 : 0 < i) : n≤offset rs i+k := by
  have hs := offset_succ rs 0 (by omega)
  have hfirst := hn (rs[0]'(by omega)) (List.getElem_mem (by omega))
  have hm := offset_mono rs 1 i (by omega) (by omega)
  simp only [offset_zero,Nat.zero_add] at hs
  omega

theorem segment_end_index_gap (rs : List Run) (n : Nat) (hn : ∀ r ∈ rs, n ≤r.2)
    (i k : Nat) (hi : i < rs.length) (hi1 : i + 1<rs.length) (hk : k ≤ (rs[i]'hi).2) :
    offset rs i+k+n≤(rs.map Prod.snd).sum := by
  have hs := offset_succ rs i hi
  have hs' := offset_succ rs (i+1) hi1
  have hnext := hn (rs[i+1]'hi1) (List.getElem_mem hi1)
  have hm := offset_le_total rs (i+1+1) (by omega)
  omega

/-- All points of every segment after the first have a quantitative gap
from the exact initial point of the expanded route. -/
theorem segment_start_distance (s n : Nat) (p : Point) (rs : List Run)
    (hs : LatticeRouteCore.IndexSeparated s (expandRuns p rs))
    (hn : ∀ r ∈ rs, n ≤r.2) (i : Nat) (hi : i < (segments p rs).length) (hi0 : 0 < i)
    (k : Nat) (hk : k ≤ ((segments p rs)[i]'hi).2.2) :
    min s n≤IntegerGrid.manhattan p (segmentPoint ((segments p rs)[i]'hi) k) := by
  have hi' : i<rs.length := by simpa only [segments_length] using hi
  rw [segments_getElem_run p rs i hi'] at hk
  rw [segmentPoint_getElem p rs i k hi' hk]
  have hh := hs 0 (offset rs i+k) (by rw [expandRuns_length]; omega)
    (offset_point_lt p rs i k hi' hk) (by omega)
  rw [expandRuns_first,Nat.sub_zero] at hh
  have hg := segment_start_index_gap rs n hn i k hi' hi0
  exact (by omega : min s n≤min s (offset rs i+k)).trans hh

/-- All points of every segment before the last have the same gap from
the exact final point of the expanded route. -/
theorem segment_end_distance (s n : Nat) (p : Point) (rs : List Run)
    (hs : LatticeRouteCore.IndexSeparated s (expandRuns p rs))
    (hn : ∀ r ∈ rs, n ≤r.2) (i : Nat) (hi : i < (segments p rs).length)
    (hi1 : i + 1<(segments p rs).length)
    (k : Nat) (hk : k ≤ ((segments p rs)[i]'hi).2.2) :
    min s n≤IntegerGrid.manhattan (segmentPoint ((segments p rs)[i]'hi) k) (runEnd p rs) := by
  have hi' : i<rs.length := by simpa only [segments_length] using hi
  have hi1' : i+1<rs.length := by simpa only [segments_length] using hi1
  rw [segments_getElem_run p rs i hi'] at hk
  rw [segmentPoint_getElem p rs i k hi' hk]
  have hg := segment_end_index_gap rs n hn i k hi' hi1' hk
  have hh := hs (offset rs i+k) (rs.map Prod.snd).sum (offset_point_lt p rs i k hi' hk)
    (by rw [expandRuns_length]; omega) (by omega)
  rw [expandRuns_last] at hh
  exact (by omega : min s n≤min s ((rs.map Prod.snd).sum-(offset rs i+k))).trans hh

end GridHardness.LatticeRouteRuns
