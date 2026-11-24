/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunsReverse
public import GridHardness.LatticeRouteIndexedSeparation

/-!
# Lattice Route Run Segments

Canonical positioned straight segments of the computed run list.
Their points are indexed points of the reconstructed route, so separation
in traversal order transfers to geometric segment clearance.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRuns
open CliffordSynthesis LatticeRouteDirections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Segment := Point × Run

def segments (p : Point) : List Run → List Segment
  | [] => []
  | (d,n)::rs => (p,(d,n))::segments (advance p d n) rs

def segmentPoint (a : Segment) (k : Nat) : Point := advance a.1 a.2.1 k

def offset (rs : List Run) (i : Nat) : Nat := ((rs.take i).map Prod.snd).sum

theorem segments_length (p : Point) (rs : List Run) : (segments p rs).length=rs.length := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih => cases r; simp [segments,ih]

theorem segments_runs (p : Point) (rs : List Run) : (segments p rs).map Prod.snd=rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih => cases r; simp [segments,ih]

theorem segments_getElem_run (p : Point) (rs : List Run) (i : Nat) (hi : i < rs.length) :
    ((segments p rs)[i]'(by rw [segments_length]; exact hi)).2=rs[i] := by
  induction rs generalizing p i with
  | nil => simp at hi
  | cons r rs ih =>
    cases r with
    | mk d n =>
      cases i with
      | zero => rfl
      | succ i => simpa only [segments,List.getElem_cons_succ] using ih (advance p d n) i (by simpa using hi)

@[simp] theorem offset_zero (rs : List Run) : offset rs 0=0 := rfl

@[simp] theorem offset_cons_succ (r : Run) (rs : List Run) (i : Nat) :
    offset (r::rs) (i+1)=r.2+offset rs i := by simp [offset]

theorem offset_succ (rs : List Run) (i : Nat) (hi : i < rs.length) :
    offset rs (i+1)=offset rs i+(rs[i]'hi).2 := by
  unfold offset
  rw [List.take_succ_eq_append_getElem hi,List.map_append,List.sum_append]
  simp

theorem offset_mono (rs : List Run) (i j : Nat) (hij : i ≤ j) (hj : j ≤ rs.length) :
    offset rs i≤offset rs j := by
  induction j generalizing i with
  | zero =>
    have hi : i=0 := by omega
    simp [hi]
  | succ j ih =>
    by_cases he : i=j+1
    · simp [he]
    · have hh := ih i (by omega) (by omega)
      rw [offset_succ rs j (by omega)]
      omega

theorem offset_le_total (rs : List Run) (i : Nat) (hi : i ≤ rs.length) :
    offset rs i≤(rs.map Prod.snd).sum := by
  simpa [offset] using offset_mono rs i rs.length hi (by omega)

theorem expandRuns_length (p : Point) (rs : List Run) :
    (expandRuns p rs).length=(rs.map Prod.snd).sum+1 := by
  rw [← expand_eq_runs,expand,walk_length,expand_length]

theorem offset_point_lt (p : Point) (rs : List Run) (i k : Nat) (hi : i < rs.length)
    (hk : k ≤ (rs[i]'hi).2) : offset rs i+k<(expandRuns p rs).length := by
  rw [expandRuns_length]
  have h := offset_le_total rs (i+1) (by omega)
  rw [offset_succ rs i hi] at h
  omega

theorem walk_prefix_getElem (p : Point) (ds es : List (Fin 4)) (k : Nat) (hk : k ≤ ds.length) :
    (walk p (ds++es))[k]'(by simp; omega)=(walk p ds)[k]'(by simp; omega) := by
  induction ds generalizing p k with
  | nil =>
    have hk0 : k=0 := by simpa using Nat.eq_zero_of_le_zero hk
    subst k
    cases es <;> rfl
  | cons d ds ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [List.cons_append,walk,List.getElem_cons_succ] using
        ih (step p d) k (by simp at hk; omega)

/-- Every point of every positioned run is the corresponding indexed point
of the reconstructed route, including the endpoint shared with the next run. -/
theorem segmentPoint_getElem (p : Point) (rs : List Run) (i k : Nat) (hi : i < rs.length)
    (hk : k ≤ (rs[i]'hi).2) :
    segmentPoint ((segments p rs)[i]'(by rw [segments_length]; exact hi)) k=
      (expandRuns p rs)[offset rs i+k]'(by
        rw [expandRuns_length]
        have h := offset_le_total rs (i+1) (by omega)
        rw [offset_succ rs i hi] at h
        omega) := by
  induction rs generalizing p i with
  | nil => simp at hi
  | cons r rs ih =>
    rcases r with ⟨d,n⟩
    cases i with
    | zero =>
      simp only [offset_zero,Nat.zero_add]
      have hklen : k<(expandRuns p ((d,n)::rs)).length := by
        simpa only [offset_zero,Nat.zero_add] using offset_point_lt p ((d,n)::rs) 0 k hi hk
      change advance p d k=(expandRuns p ((d,n)::rs))[k]'hklen
      simp only [← expand_eq_runs,expand]
      simp only [List.getElem_cons_zero] at hk
      change advance p d k=(walk p (List.replicate n d++expandDirections rs))[k]'(by simp; omega)
      rw [walk_prefix_getElem p (List.replicate n d) (expandDirections rs) k (by simpa using hk)]
      exact (walk_replicate_getElem p d n k (by simpa using hk)).symm
    | succ i =>
      have hi' : i<rs.length := by simpa using hi
      have hh := ih (advance p d n) i hi' (by simpa using hk)
      simp only [segments,List.getElem_cons_succ,offset_cons_succ,expandRuns]
      rw [List.getElem_append_right (by simp [walkInit_replicate]; omega)]
      simpa [walkInit_replicate,Nat.add_assoc] using hh

/-- An intervening complete run separates the traversal intervals of
nonconsecutive segments by at least its length. -/
theorem segment_index_gap (rs : List Run) (n : Nat)
    (hn : ∀ r ∈ rs, n ≤r.2) (i j k m : Nat) (hi : i < rs.length) (hj : j < rs.length)
    (hij : i + 1<j) (hk : k ≤ (rs[i]'hi).2) :
    offset rs i+k+n≤offset rs j+m := by
  have hs := offset_succ rs i hi
  have hs' := offset_succ rs (i+1) (by omega)
  have hl := hn (rs[i+1]'(by omega)) (List.getElem_mem (by omega))
  have hm := offset_mono rs (i+1+1) j (by omega) (by omega)
  omega

/-- Nonconsecutive positioned segments inherit quantitative clearance
from route-index separation and the computed minimum run length. -/
theorem segments_index_distance (s n : Nat) (p : Point) (rs : List Run)
    (hs : LatticeRouteCore.IndexSeparated s (expandRuns p rs))
    (hn : ∀ r ∈ rs, n ≤r.2) (i j : Nat) (hi : i < (segments p rs).length)
    (hj : j < (segments p rs).length) (hij : i + 1<j)
    (k m : Nat) (hk : k ≤ ((segments p rs)[i]'hi).2.2)
    (hm : m ≤ ((segments p rs)[j]'hj).2.2) :
    min s n≤IntegerGrid.manhattan
      (segmentPoint ((segments p rs)[i]'hi) k) (segmentPoint ((segments p rs)[j]'hj) m) := by
  have hi' : i<rs.length := by simpa only [segments_length] using hi
  have hj' : j<rs.length := by simpa only [segments_length] using hj
  rw [segments_getElem_run p rs i hi'] at hk
  rw [segments_getElem_run p rs j hj'] at hm
  rw [segmentPoint_getElem p rs i k hi' hk,segmentPoint_getElem p rs j m hj' hm]
  have hgap := segment_index_gap rs n hn i j k m hi' hj' hij hk
  have hh := hs (offset rs i+k) (offset rs j+m)
    (offset_point_lt p rs i k hi' hk) (offset_point_lt p rs j m hj' hm) (by omega)
  have hmin : min s n≤min s ((offset rs j+m)-(offset rs i+k)) := by omega
  exact hmin.trans hh

end GridHardness.LatticeRouteRuns
