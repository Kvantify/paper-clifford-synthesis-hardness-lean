/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunsTrim

/-!
# Lattice Route Runs Reverse

Reversing a geometric route reverses its computed maximal straight runs
and reverses each cardinal direction, preserving every run length.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRuns
open LatticeRouteDirections
set_option autoImplicit false

/-- The cardinal direction pointing backwards. -/
def opposite (d : Fin 4) : Fin 4 := ⟨(d.val+2)%4, Nat.mod_lt _ (by decide)⟩

@[simp] theorem opposite_opposite (d : Fin 4) : opposite (opposite d)=d := by
  fin_cases d <;> decide

theorem opposite_injective : Function.Injective opposite := by
  intro d e he
  simpa using congrArg opposite he

theorem step_opposite (p : Point) (d : Fin 4) : step (step p d) (opposite d)=p := by
  fin_cases d <;> simp [opposite,step,DirectedLocalLayout.ray]

theorem direction_reverse (p q : Point) (h : UnitStep p q) :
    direction q p=opposite (direction p q) := by
  apply (direction_unique q p (unitStep_symm h) _).mp
  conv_rhs => rw [direction_spec p q h]
  rw [direction_step]
  exact (step_opposite p (direction p q)).symm

theorem directions_append_point (l : List Point) (p q : Point)
    (hl : l.getLast? =some q) :
    directions (l++[p])=directions l++[direction q p] := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    cases l with
    | nil =>
      have he : a=q := by simpa using hl
      simp [directions,he]
    | cons b l =>
      simpa only [List.cons_append,directions] using
        congrArg (List.cons (direction a b)) (ih (by simpa using hl))

theorem directions_reverse (l : List Point) (hc : l.IsChain UnitStep) :
    directions l.reverse=((directions l).reverse).map opposite := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases l with
    | nil => rfl
    | cons q l =>
      rw [List.reverse_cons,directions_append_point _ p q (by simp),ih hc.tail]
      rw [directions,List.reverse_cons,List.map_append,List.map_singleton]
      rw [direction_reverse p q (List.isChain_cons_cons.mp hc).1]

theorem prepend_map (f : Fin 4 → Fin 4) (hf : Function.Injective f)
    (d : Fin 4) (rs : List Run) :
    prepend (f d) (rs.map (fun r => (f r.1,r.2)))=
      (prepend d rs).map (fun r => (f r.1,r.2)) := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    rcases r with ⟨e,n⟩
    by_cases he : d=e
    · simp [prepend,he]
    · have hfne : f d≠f e := fun h => he (hf h)
      simp [prepend,he,hfne]

theorem compress_map (f : Fin 4 → Fin 4) (hf : Function.Injective f)
    (ds : List (Fin 4)) :
    compressDirections (ds.map f)=
      (compressDirections ds).map (fun r => (f r.1,r.2)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons,compressDirections,ih,prepend_map f hf]

/-- Reversal preserves each computed run length exactly, while reversing
both the run order and the direction of travel. -/
theorem compress_route_reverse (l : List Point) (hc : l.IsChain UnitStep) :
    compress l.reverse=(compress l).reverse.map (fun r => (opposite r.1,r.2)) := by
  rw [compress,directions_reverse l hc,compress_map opposite opposite_injective,
    compress_reverse]
  rfl

theorem runs_reverse_lower (l : List Point) (hc : l.IsChain UnitStep) (n : Nat)
    (h : ∀ r ∈compress l, n≤r.2) : ∀ r∈compress l.reverse,n≤r.2 := by
  intro r hr
  rw [compress_route_reverse l hc] at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  exact h q (List.mem_reverse.mp hq)

theorem runs_orient_lower (l : List Point) (hc : l.IsChain UnitStep) (n : Nat)
    (h : ∀ r ∈compress l, n≤r.2) (b : Bool) :
    ∀ r∈compress (orient l b),n≤r.2 := by
  cases b
  · exact h
  · exact runs_reverse_lower l hc n h

end GridHardness.LatticeRouteRuns
