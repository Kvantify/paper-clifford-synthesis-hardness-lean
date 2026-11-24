/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunsSubdivision

/-!
# Lattice Route Runs Trim

Quantitative preservation of computed straight-run lengths under taking
contiguous portions of a route. Removing endpoint points can shorten a maximal
run by at most the total number of removed points.
-/

public section

namespace GridHardness.LatticeRouteRuns
open LatticeRouteDirections
set_option autoImplicit false

/-- Positive run lists with different neighboring directions are already in
normal form for the implemented run-length encoder. -/
theorem compress_expandDirections (rs : List Run)
    (hp : ∀ r ∈rs, 0 <r.2) (hm : (rs.map Prod.fst).IsChain (· ≠·)) :
    compressDirections (expandDirections rs)=rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨d,n⟩
    have hn : 0<n := hp (d,n) (by simp)
    have hp' : ∀ r∈rs,0<r.2 := fun r hr => hp r (by simp [hr])
    have hm' : (rs.map Prod.fst).IsChain (·≠·) := hm.tail
    simp only [expandDirections,List.flatMap_cons]
    rw [compress_replicate_append n hn]
    change (match compressDirections (expandDirections rs) with
      | [] => [(d,n)]
      | (e,k)::rs => if d=e then (e,n+k)::rs else (d,n)::(e,k)::rs) = _
    rw [ih hp' hm']
    cases rs with
    | nil => rfl
    | cons r rs =>
      rcases r with ⟨e,k⟩
      have hde : d≠e := (List.isChain_cons_cons.mp hm).1
      simp [hde]

theorem expandDirections_reverse (rs : List Run) :
    expandDirections rs.reverse=(expandDirections rs).reverse := by
  simp only [expandDirections,List.flatMap_reverse]
  congr 1
  congr 1
  funext r
  simp

/-- Reversing a direction list reverses its computed run list. -/
theorem compress_reverse (ds : List (Fin 4)) :
    compressDirections ds.reverse=(compressDirections ds).reverse := by
  have hp : ∀ r∈(compressDirections ds).reverse,0<r.2 := by
    intro r hr
    exact compress_positive ds r (List.mem_reverse.mp hr)
  have hm : (((compressDirections ds).reverse).map Prod.fst).IsChain (·≠·) := by
    rw [List.map_reverse]
    exact List.isChain_reverse.mpr ((compress_maximal ds).imp fun _ _ h => Ne.symm h)
  have h := compress_expandDirections (compressDirections ds).reverse hp hm
  simpa [expandDirections_reverse,expand_compress] using h

/-- Deleting one initial direction shortens a run by at most one. -/
theorem compress_tail_lower (d : Fin 4) (ds : List (Fin 4)) (n : Nat)
    (h : ∀ r ∈compressDirections (d::ds), n≤r.2) :
    ∀ r∈compressDirections ds,n-1≤r.2 := by
  cases he : compressDirections ds with
  | nil => simp
  | cons q rs =>
    rcases q with ⟨e,k⟩
    by_cases hd : d=e
    · subst e
      have hk := h (d,k+1) (by simp [compressDirections,he,prepend])
      intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · cases hr
        dsimp at hk ⊢
        omega
      · have hh := h r (by simp [compressDirections,he,prepend,hr])
        omega
    · intro r hr
      have hh := h r (by simp only [compressDirections,he,prepend,hd,ite_false]; simp [hr])
      omega

/-- Removing `a` initial directions shortens every surviving maximal run
by at most `a`. -/
theorem compress_drop_lower (a : Nat) (ds : List (Fin 4)) (n : Nat)
    (h : ∀ r ∈compressDirections ds, n≤r.2) :
    ∀ r∈compressDirections (ds.drop a),n-a≤r.2 := by
  induction a generalizing ds n with
  | zero => simpa using h
  | succ a ih =>
    cases ds with
    | nil => simp [compressDirections]
    | cons d ds =>
      have hh := ih ds (n-1) (compress_tail_lower d ds n h)
      simpa [Nat.sub_sub,Nat.add_comm] using hh

/-- Truncating a direction list loses at most its omitted terminal length
from any surviving maximal run. -/
theorem compress_take_lower (k : Nat) (ds : List (Fin 4)) (n : Nat)
    (h : ∀ r ∈compressDirections ds, n≤r.2) :
    ∀ r∈compressDirections (ds.take k),n-(ds.length-k)≤r.2 := by
  have hr : ∀ r∈compressDirections ds.reverse,n≤r.2 := by
    simpa only [compress_reverse,List.mem_reverse] using h
  have hh := compress_drop_lower (ds.length-k) ds.reverse n hr
  intro r hmem
  apply hh r
  rw [← List.reverse_take,compress_reverse]
  simpa using hmem

/-- The computed runs of a contiguous portion have the expected lower bound. -/
theorem compress_trim_lower (a b : Nat) (ds : List (Fin 4)) (n : Nat)
    (h : ∀ r ∈compressDirections ds, n≤r.2) :
    ∀ r∈compressDirections (LatticeRouteTrim.trim a b ds),n-a-b≤r.2 := by
  have hd := compress_drop_lower a ds n h
  have ht := compress_take_lower (ds.length-a-b) (ds.drop a) (n-a) hd
  intro r hr
  have hh := ht r hr
  simp only [List.length_drop] at hh
  omega

theorem directions_drop (a : Nat) (l : List Point) :
    directions (l.drop a)=(directions l).drop a := by
  induction a generalizing l with
  | zero => rfl
  | succ a ih =>
    cases l with
    | nil => simp [directions]
    | cons p l =>
      cases l with
      | nil => simp [directions]
      | cons q l => simpa [directions] using ih (q::l)

theorem directions_take (k : Nat) (l : List Point) :
    directions (l.take k)=(directions l).take (k-1) := by
  induction k generalizing l with
  | zero => simp [directions]
  | succ k ih =>
    cases k with
    | zero => cases l <;> simp [directions]
    | succ k =>
      cases l with
      | nil => simp [directions]
      | cons p l =>
        cases l with
        | nil => simp [directions]
        | cons q l => simpa [directions] using congrArg (List.cons (direction p q)) (ih (q::l))

theorem directions_trim (a b : Nat) (l : List Point) :
    directions (LatticeRouteTrim.trim a b l)=
      LatticeRouteTrim.trim a b (directions l) := by
  simp only [LatticeRouteTrim.trim,directions_take,directions_drop,directions_length]
  congr 1
  omega

/-- Endpoint trimming decreases the minimum computed straight-run length
by at most the total number of removed endpoint points. -/
theorem runs_trim_lower (a b : Nat) (l : List Point) (n : Nat)
    (h : ∀ r ∈compress l, n≤r.2) :
    ∀ r∈compress (LatticeRouteTrim.trim a b l),n-a-b≤r.2 := by
  simpa only [compress,directions_trim] using compress_trim_lower a b (directions l) n h

/-- Every maximal straight run in the actual dilated, trimmed corridor has
length at least the scale minus the two endpoint cuts. -/
theorem core_runs_long (s a b : Nat) (hs : 0 <s) (l : List Point)
    (hc : l.IsChain UnitStep) :
    ∀ r∈compress (LatticeRouteCore.core s a b l),s-a-b≤r.2 :=
  runs_trim_lower a b (LatticeSubdivision.subdivide s l) s
    (subdivide_runs_long s hs l hc)

theorem core64_runs_long (l : List Point) (hc : l.IsChain UnitStep) :
    ∀ r∈compress (LatticeRouteCore.core 64 8 8 l),48≤r.2 :=
  core_runs_long 64 8 8 (by decide) l hc

end GridHardness.LatticeRouteRuns
