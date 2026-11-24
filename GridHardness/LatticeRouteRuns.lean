/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteDirections
public import GridHardness.LatticeRouteSubdivision

/-!
# Lattice Route Runs

Effective compression of unit lattice routes into maximal straight
runs. The implementation records a cardinal direction and a positive step
count for each run; expanding the result reconstructs the input route.
No run decomposition is supplied as a hypothesis.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRuns
open LatticeRouteDirections
set_option autoImplicit false

abbrev Point := Int × Int
abbrev Run := Fin 4 × Nat

/-- Add one step, extending the first run exactly when its direction agrees. -/
def prepend (d : Fin 4) : List Run → List Run
  | [] => [(d,1)]
  | (e,n)::rs => if d=e then (e,n+1)::rs else (d,1)::(e,n)::rs

/-- Run-length encoding of a list of cardinal directions. -/
def compressDirections : List (Fin 4) → List Run
  | [] => []
  | d::ds => prepend d (compressDirections ds)

def expandDirections (rs : List Run) : List (Fin 4) :=
  rs.flatMap (fun r => List.replicate r.2 r.1)

theorem expand_prepend (d : Fin 4) (rs : List Run) :
    expandDirections (prepend d rs)=d::expandDirections rs := by
  cases rs with
  | nil => simp [prepend,expandDirections]
  | cons r rs =>
    rcases r with ⟨e,n⟩
    by_cases h : d=e
    · subst d
      simp [prepend,expandDirections,List.replicate_succ]
    · simp [prepend,h,expandDirections]

/-- Compression loses no steps, including their order. -/
theorem expand_compress (ds : List (Fin 4)) :
    expandDirections (compressDirections ds)=ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [compressDirections,expand_prepend,ih]

theorem compress_positive (ds : List (Fin 4)) :
    ∀ r∈compressDirections ds, 0<r.2 := by
  induction ds with
  | nil => simp [compressDirections]
  | cons d ds ih =>
    simp only [compressDirections]
    cases h : compressDirections ds with
    | nil => simp [prepend]
    | cons r rs =>
      rcases r with ⟨e,n⟩
      by_cases he : d=e
      · simp only [prepend,he,ite_eq_left,List.mem_cons,forall_eq_or_imp]
        exact ⟨by omega,fun r hr => ih r (by rw [h]; simp [hr])⟩
      · simp only [prepend,he,ite_false,List.mem_cons,forall_eq_or_imp]
        exact ⟨by decide,ih (e,n) (by rw [h]; simp),fun r hr => ih r (by rw [h]; simp [hr])⟩

/-- Consecutive compressed runs always have different directions. -/
theorem compress_maximal (ds : List (Fin 4)) :
    ((compressDirections ds).map Prod.fst).IsChain (·≠·) := by
  induction ds with
  | nil => simp [compressDirections]
  | cons d ds ih =>
    simp only [compressDirections]
    cases h : compressDirections ds with
    | nil => simp [prepend]
    | cons r rs =>
      rcases r with ⟨e,n⟩
      rw [h] at ih
      by_cases he : d=e
      · subst d
        simpa [prepend] using ih
      · simpa [prepend,he,List.isChain_cons_cons] using And.intro he ih

theorem expand_length (rs : List Run) :
    (expandDirections rs).length=(rs.map Prod.snd).sum := by
  simp [expandDirections,List.length_flatMap]

theorem compress_step_count (ds : List (Fin 4)) :
    ((compressDirections ds).map Prod.snd).sum=ds.length := by
  rw [← expand_length,expand_compress]

theorem compress_count_le (ds : List (Fin 4)) :
    (compressDirections ds).length≤ds.length := by
  induction ds with
  | nil => simp [compressDirections]
  | cons d ds ih =>
    simp only [compressDirections]
    cases h : compressDirections ds with
    | nil => simp [prepend]
    | cons r rs =>
      rcases r with ⟨e,n⟩
      rw [h] at ih
      by_cases he : d=e <;> simp [prepend,he] <;> simp at ih <;> omega

/-- Cardinal directions of the consecutive input steps. -/
def directions : List Point → List (Fin 4)
  | [] => []
  | [_] => []
  | a::b::l => direction a b::directions (b::l)

/-- Explicit vertices visited by a direction list, including the start. -/
def walk (p : Point) : List (Fin 4) → List Point
  | [] => [p]
  | d::ds => p::walk (step p d) ds

def compress (l : List Point) : List Run := compressDirections (directions l)

def expand (p : Point) (rs : List Run) : List Point := walk p (expandDirections rs)

theorem directions_length (l : List Point) : (directions l).length=l.length-1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp [directions,ih]

theorem walk_directions (a : Point) (l : List Point)
    (hc : (a::l).IsChain UnitStep) : walk a (directions (a::l))=a::l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    have hab := (List.isChain_cons_cons.mp hc).1
    simp only [directions,walk]
    rw [← direction_spec a b hab,ih b hc.tail]

/-- The generated straight runs expand to exactly the original lattice
route. In particular they preserve every original vertex and turn. -/
theorem expand_compress_route (a : Point) (l : List Point)
    (hc : (a::l).IsChain UnitStep) : expand a (compress (a::l))=a::l := by
  rw [expand,compress,expand_compress]
  exact walk_directions a l hc

theorem runs_positive (l : List Point) : ∀ r∈compress l, 0<r.2 :=
  compress_positive (directions l)

theorem runs_maximal (l : List Point) :
    ((compress l).map Prod.fst).IsChain (·≠·) := compress_maximal (directions l)

theorem run_step_count (l : List Point) :
    ((compress l).map Prod.snd).sum=l.length-1 := by
  rw [compress,compress_step_count,directions_length]

theorem run_count_le (l : List Point) : (compress l).length≤l.length-1 := by
  simpa [compress,directions_length] using compress_count_le (directions l)

theorem compress_head (ds : List (Fin 4)) :
    ((compressDirections ds).map Prod.fst).head?=ds.head? := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    simp only [compressDirections]
    cases h : compressDirections ds with
    | nil => simp [prepend]
    | cons r rs =>
      rcases r with ⟨e,n⟩
      by_cases he : d=e <;> simp [prepend,he]

/-- Any relation holding at all original step transitions still holds
at the boundaries of the compressed runs. -/
theorem compress_preserves_chain (R : Fin 4 → Fin 4 → Prop) (ds : List (Fin 4))
    (hc : ds.IsChain R) : ((compressDirections ds).map Prod.fst).IsChain R := by
  induction ds with
  | nil => simp [compressDirections]
  | cons d ds ih =>
    simp only [compressDirections]
    have ht := ih hc.tail
    cases h : compressDirections ds with
    | nil => simp [prepend]
    | cons r rs =>
      rcases r with ⟨e,n⟩
      rw [h] at ht
      by_cases he : d=e
      · subst d
        simpa [prepend] using ht
      · have hed : e∈ds.head? := by
          rw [← compress_head ds,h]
          simp
        have hde := hc.rel_head? hed
        simpa [prepend,he,List.isChain_cons_cons] using And.intro hde ht

/-- Adjacent distinct vertices cannot produce an immediate reversal in
a simple lattice route. Equal directions or a quarter-turn remain. -/
theorem direction_turn (a b c : Point) (hab : UnitStep a b) (hbc : UnitStep b c)
    (hac : a ≠c) : direction a b=direction b c ∨
      (direction a b).val%2≠(direction b c).val%2 := by
  have hb := direction_spec a b hab
  have hc := direction_spec b c hbc
  generalize direction a b=d at *
  generalize direction b c=e at *
  by_contra hn
  push Not at hn
  obtain ⟨hne,hpar⟩ := hn
  fin_cases d <;> fin_cases e
  all_goals norm_num at hne
  all_goals norm_num at hpar
  all_goals apply hac
  all_goals rw [hc,hb]
  all_goals simp [step,DirectedLocalLayout.ray]

theorem directions_turns (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) :
    (directions l).IsChain (fun d e => d=e ∨ d.val%2≠e.val%2) := by
  induction l with
  | nil => simp [directions]
  | cons a l ih =>
    cases l with
    | nil => simp [directions]
    | cons b l =>
      cases l with
      | nil => simp [directions]
      | cons c l =>
        have ha := (List.nodup_cons.mp hn).1
        have hac : a≠c := fun he => ha (by simp [he])
        have ht := ih hn.tail hc.tail
        simp only [directions,List.isChain_cons_cons] at ht ⊢
        exact ⟨direction_turn a b c (List.isChain_cons_cons.mp hc).1
          (List.isChain_cons_cons.mp hc.tail).1 hac,ht⟩

/-- For a simple unit route, every transition between maximal straight
runs is a genuine right-angle turn, never a reversal. -/
theorem runs_perpendicular (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) :
    ((compress l).map Prod.fst).IsChain (fun d e => d.val%2≠e.val%2) := by
  have ht := compress_preserves_chain _ (directions l) (directions_turns l hn hc)
  have hm := runs_maximal l
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have ht' := List.isChain_iff_getElem.mp ht i hi
  have hm' := List.isChain_iff_getElem.mp hm i hi
  exact ht'.resolve_left hm'

/-- Move by a whole straight run in the chosen cardinal direction. -/
def advance (p : Point) (d : Fin 4) (n : Nat) : Point :=
  (p.1+(DirectedLocalLayout.ray d n).1,p.2+(DirectedLocalLayout.ray d n).2)

@[simp] theorem advance_zero (p : Point) (d : Fin 4) : advance p d 0=p := by
  fin_cases d <;> simp [advance,DirectedLocalLayout.ray]

theorem advance_step (p : Point) (d : Fin 4) (n : Nat) :
    advance (step p d) d n=advance p d (n+1) := by
  fin_cases d <;> simp [advance,step,DirectedLocalLayout.ray] <;> omega

theorem advance_ne (p : Point) (d : Fin 4) (n : Nat) (hn : 0 <n) : advance p d n≠p := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases d <;> simp [advance,DirectedLocalLayout.ray] at hx hy <;> omega

@[simp] theorem walk_length (p : Point) (ds : List (Fin 4)) :
    (walk p ds).length=ds.length+1 := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [walk,ih]

/-- Every point in a straight run has its direct cardinal coordinate. -/
theorem walk_replicate_getElem (p : Point) (d : Fin 4) (n k : Nat) (hk : k ≤n) :
    (walk p (List.replicate n d))[k]'(by simp; omega)=advance p d k := by
  induction n generalizing p k with
  | zero =>
    have hk0 : k=0 := by omega
    subst k
    simp [walk]
  | succ n ih =>
    cases k with
    | zero => simp [walk,List.replicate_succ]
    | succ k =>
      simp only [List.replicate_succ,walk,List.getElem_cons_succ]
      rw [ih (step p d) k (by omega),advance_step]

/-- A straight run is exactly the ordered set of cardinal offsets
from zero through its run length. -/
theorem walk_replicate (p : Point) (d : Fin 4) (n : Nat) :
    walk p (List.replicate n d)=(List.range (n+1)).map (advance p d) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [walk_replicate_getElem p d n i (by simpa using hi)]
    simp

/-- The terminal coordinate after a list of directed unit steps. -/
def finish (p : Point) : List (Fin 4) → Point
  | [] => p
  | d::ds => finish (step p d) ds

theorem finish_replicate (p : Point) (d : Fin 4) (n : Nat) :
    finish p (List.replicate n d)=advance p d n := by
  induction n generalizing p with
  | zero => simp [finish]
  | succ n ih => simp [List.replicate_succ,finish,ih,advance_step]

theorem walk_getLast (p : Point) (ds : List (Fin 4)) :
    (walk p ds).getLast?=some (finish p ds) := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [walk,finish]
    cases ds with
    | nil => rfl
    | cons e ds => simpa [walk] using ih (step p d)

/-- The half-open list of points visited by a direction sequence. -/
def walkInit (p : Point) : List (Fin 4) → List Point
  | [] => []
  | d::ds => p::walkInit (step p d) ds

theorem walk_append (p : Point) (ds es : List (Fin 4)) :
    walk p (ds++es)=walkInit p ds++walk (finish p ds) es := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [walk,walkInit,finish,ih]

/-- Expand whole straight runs, carrying their computed end coordinates
to the next run and including shared endpoints exactly once. -/
def expandRuns (p : Point) : List Run → List Point
  | [] => [p]
  | (d,n)::rs => walkInit p (List.replicate n d)++expandRuns (advance p d n) rs

theorem expand_eq_runs (p : Point) (rs : List Run) : expand p rs=expandRuns p rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨d,n⟩
    simp only [expand,expandDirections,List.flatMap_cons]
    rw [walk_append,finish_replicate]
    exact congrArg (fun l => walkInit p (List.replicate n d)++l) (ih (advance p d n))

/-- The explicit straight-run constructor reconstructs every nonempty
unit route, using only its computed run list and initial point. -/
theorem expandRuns_compress (a : Point) (l : List Point)
    (hc : (a::l).IsChain UnitStep) : expandRuns a (compress (a::l))=a::l := by
  rw [← expand_eq_runs,expand_compress_route a l hc]

theorem compress_ne_nil (l : List Point) (hl : 2 ≤l.length) : compress l≠[] := by
  intro he
  have hlen := run_step_count l
  rw [he] at hlen
  simp at hlen
  omega

/-- A complete certificate for the computed run decomposition. It
requires only the original route's simplicity and unit-step property. -/
theorem compression_certificate (a : Point) (l : List Point)
    (hn : (a::l).Nodup) (hc : (a::l).IsChain UnitStep) :
    expandRuns a (compress (a::l))=a::l ∧
    (∀ r∈compress (a::l), 0<r.2) ∧
    ((compress (a::l)).map Prod.fst).IsChain (fun d e => d.val%2≠e.val%2) ∧
    ((compress (a::l)).map Prod.snd).sum=l.length ∧
    (compress (a::l)).length≤l.length := by
  exact ⟨expandRuns_compress a l hc,runs_positive (a::l),runs_perpendicular (a::l) hn hc,
    by simpa using run_step_count (a::l),by simpa using run_count_le (a::l)⟩

end GridHardness.LatticeRouteRuns
