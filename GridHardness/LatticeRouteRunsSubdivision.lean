/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRuns
public import GridHardness.LatticeRouteCore

/-!
# Lattice Route Runs Subdivision

Exact straight-run lengths under integer dilation and endpoint trimming.
The decomposition is the computed maximal-run encoding, not extra input.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRuns
open LatticeRouteDirections
set_option autoImplicit false

/-- Repeat each direction once for every new unit edge. -/
def dilateDirections (s : Nat) (ds : List (Fin 4)) : List (Fin 4) :=
  ds.flatMap (List.replicate s)

theorem directions_walk (p : Point) (ds : List (Fin 4)) :
    directions (walk p ds)=ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    cases ds with
    | nil => simp [walk,directions,direction_step]
    | cons e ds => simpa [walk,directions,direction_step] using ih (step p d)

theorem walkInit_replicate (p : Point) (d : Fin 4) (n : Nat) :
    walkInit p (List.replicate n d)=(List.range n).map (advance p d) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,walkInit,List.range_succ_eq_map,List.map_cons,
      List.map_map,advance_zero,ih]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact advance_step p d i

theorem interpolate_step_eq_advance (s : Nat) (p : Point) (d : Fin 4) (k : Nat) :
    LatticeSubdivision.interpolate s p (step p d) k=
      advance (LatticeSubdivision.scale s p) d k := by
  fin_cases d <;>
    simp [LatticeSubdivision.interpolate,LatticeSubdivision.scale,step,advance,
      DirectedLocalLayout.ray]

theorem advance_scaled_step (s : Nat) (p : Point) (d : Fin 4) :
    advance (LatticeSubdivision.scale s p) d s=LatticeSubdivision.scale s (step p d) := by
  fin_cases d <;>
    simp [LatticeSubdivision.scale,step,advance,DirectedLocalLayout.ray] <;> ring

theorem subdivide_walk (s : Nat) (p : Point) (ds : List (Fin 4)) :
    LatticeSubdivision.subdivide s (walk p ds)=
      walk (LatticeSubdivision.scale s p) (dilateDirections s ds) := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    have hseg : LatticeSubdivision.segmentInit s p (step p d)=
        walkInit (LatticeSubdivision.scale s p) (List.replicate s d) := by
      rw [walkInit_replicate]
      simp only [LatticeSubdivision.segmentInit]
      apply List.map_congr_left
      intro i hi
      exact interpolate_step_eq_advance s p d i
    simp only [dilateDirections,List.flatMap_cons]
    rw [walk_append,finish_replicate,advance_scaled_step]
    cases ds with
    | nil => simpa [walk,LatticeSubdivision.subdivide] using
        congrArg (fun l => l++[LatticeSubdivision.scale s (step p d)]) hseg
    | cons e ds =>
      simpa only [walk,LatticeSubdivision.subdivide,hseg,dilateDirections] using
        congrArg (fun l => walkInit (LatticeSubdivision.scale s p)
          (List.replicate s d)++l) (ih (step p d))

/-- Subdivision repeats the actual input direction list exactly. -/
theorem directions_subdivide (s : Nat) (l : List Point)
    (hc : l.IsChain UnitStep) :
    directions (LatticeSubdivision.subdivide s l)=dilateDirections s (directions l) := by
  cases l with
  | nil => rfl
  | cons p l =>
    rw [← walk_directions p l hc,subdivide_walk,directions_walk,directions_walk]

/-- Adding a nonempty constant block extends just the first matching run. -/
theorem compress_replicate_append (n : Nat) (hn : 0 <n) (d : Fin 4)
    (ds : List (Fin 4)) :
    compressDirections (List.replicate n d++ds)=
      match compressDirections ds with
      | [] => [(d,n)]
      | (e,k)::rs => if d=e then (e,n+k)::rs else (d,n)::(e,k)::rs := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      cases h : compressDirections ds with
      | nil => simp [List.replicate_succ,compressDirections,prepend,h]
      | cons r rs =>
        rcases r with ⟨e,k⟩
        simp [List.replicate_succ,compressDirections,prepend,h,Nat.add_comm]
    | succ n =>
      rw [List.replicate_succ,List.cons_append,compressDirections,ih (by omega)]
      cases h : compressDirections ds with
      | nil => simp [prepend]
      | cons r rs =>
        rcases r with ⟨e,k⟩
        by_cases he : d=e
        · simp [he,prepend,Nat.add_comm,Nat.add_left_comm]
        · simp [he,prepend]

/-- Dilation multiplies every computed maximal run length by exactly `s`. -/
theorem compress_dilateDirections (s : Nat) (hs : 0 <s) (ds : List (Fin 4)) :
    compressDirections (dilateDirections s ds)=
      (compressDirections ds).map (fun r => (r.1,s*r.2)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [dilateDirections,List.flatMap_cons,compress_replicate_append s hs]
    change (match compressDirections (dilateDirections s ds) with
      | [] => [(d,s)]
      | (e,k)::rs => if d=e then (e,s+k)::rs else (d,s)::(e,k)::rs) = _
    rw [ih]
    cases h : compressDirections ds with
    | nil => simp [compressDirections,h,prepend]
    | cons r rs =>
      rcases r with ⟨e,k⟩
      by_cases he : d=e <;>
        simp [compressDirections,h,prepend,he,Nat.mul_add,Nat.add_comm]

/-- Exact run list of the dilated route. No simplicity assumption is needed. -/
theorem compress_subdivide (s : Nat) (hs : 0 <s) (l : List Point)
    (hc : l.IsChain UnitStep) :
    compress (LatticeSubdivision.subdivide s l)=
      (compress l).map (fun r => (r.1,s*r.2)) := by
  rw [compress,directions_subdivide s l hc,compress_dilateDirections s hs]
  rfl

theorem subdivide_runs_long (s : Nat) (hs : 0 <s) (l : List Point)
    (hc : l.IsChain UnitStep) (r : Run) (hr : r ∈compress (LatticeSubdivision.subdivide s l)) :
    s≤r.2 := by
  rw [compress_subdivide s hs l hc] at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  have hqpos := runs_positive l q hq
  dsimp
  nlinarith

end GridHardness.LatticeRouteRuns
