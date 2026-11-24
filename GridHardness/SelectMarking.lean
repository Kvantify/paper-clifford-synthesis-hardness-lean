/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridCycle

/-!
# Select Marking

Polynomial selection of a degree-two marking for arbitrary grid-cycle
inputs. All loops range over input vertices, never coordinate magnitudes.
The search enumerates vertex pairs, not Hamiltonian walks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness
open CliffordComplexity CliffordSynthesis
open GridProblems GridProblems.GridCode

private theorem range_map {α : Type} (f : Nat → α) (n : Nat) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

def pointAt : Code InputTy PointTy :=
  .pair (.pair (lookupNat PointTy (.comp .fst .fst)) (lookupNat PointTy (.comp .fst .snd)))
    (.pair (lookupNat PointTy (.comp .snd .fst)) (lookupNat PointTy (.comp .snd .snd)))

theorem pointAt_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote) (s : Fin (m + 1)) :
    pointAt.eval (input p s) = p s := by
  unfold pointAt
  simp only [Code.eval, input, lookupNat_eval PointTy _ (List.ofFn p) s.val (by simpa using s.isLt),
    List.getElem_ofFn]

def swapEntry : Code (.pair InputTy IndexedPointTy) PointTy :=
  .branch (.comp (.pair (.comp .snd .snd) (.const .nat 0)) .natEq)
    (.comp .fst pointAt)
    (.branch (.comp (.pair (.comp .snd .snd) (.comp .fst .snd)) .natEq)
      (.comp .fst start) (.comp .snd .fst))

def swapStart : Code InputTy CycleInputTy :=
  .comp (.pair .id (.comp .fst .listEnum)) (.listMapEnv swapEntry)

theorem swapStart_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote) (s : Fin (m + 1)) :
    swapStart.eval (input p s) = List.ofFn (p ∘ Equiv.swap 0 s) := by
  change ((List.ofFn p).zipIdx.map (fun q => swapEntry.eval (input p s, q))) = _
  rw [zipIdx_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (if decide (i.val = 0) then pointAt.eval (input p s) else
    if decide (i.val = s.val) then start.eval (input p s) else p i) = _
  rw [pointAt_eval, start_eval]
  simp only [Function.comp_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.val_zero, decide_eq_true_eq]
  by_cases h0 : i.val = 0 <;> by_cases hs : i.val = s.val <;> simp [h0, hs, apply_ite]
  all_goals split <;> simp_all

def markingsAt : Code InputTy (.list InputTy) :=
  .comp (.pair swapStart (.comp .fst Code.indices)) (.listMapEnv .id)

def allMarkings : Code CycleInputTy (.list InputTy) :=
  .comp (.pair .id Code.indices) (.comp (.listMapEnv markingsAt) .listJoin)

theorem markingsAt_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (s : Fin (m + 1)) : markingsAt.eval (input p s) =
      List.ofFn (fun t => input (p ∘ Equiv.swap 0 s) t) := by
  change (Code.indices.eval (List.ofFn p)).map (fun t => (swapStart.eval (input p s), t)) = _
  rw [swapStart_eval, indices_eval, List.length_ofFn, range_map]
  rfl

theorem allMarkings_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote) :
    allMarkings.eval (List.ofFn p) =
      (List.ofFn (fun s => List.ofFn (fun t => input (p ∘ Equiv.swap 0 s) t))).flatten := by
  change ((Code.indices.eval (List.ofFn p)).map
    (fun s => markingsAt.eval (List.ofFn p, s))).flatten = _
  rw [indices_eval, List.length_ofFn, range_map]
  congr 1
  apply congrArg List.ofFn
  funext s
  exact markingsAt_eval p s

theorem mem_allMarkings {m : Nat} (p : Fin (m + 1) → PointTy.denote) (x : InputTy.denote) :
    x ∈ allMarkings.eval (List.ofFn p) ↔
      ∃ s t : Fin (m + 1), x = input (p ∘ Equiv.swap 0 s) t := by
  rw [allMarkings_eval]
  constructor
  · intro hx
    obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨t, ht⟩ := List.mem_ofFn.mp hx
    exact ⟨s, t, ht.symm⟩
  · rintro ⟨s, t, rfl⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨s, rfl⟩, List.mem_ofFn.mpr ⟨t, rfl⟩⟩

def goodMarkings : Code CycleInputTy (.list InputTy) :=
  .comp allMarkings (.listFilter markedGuard)

/-- Read a first element with the canonical no-instance as default. -/
def firstMarking : Code (.list InputTy) InputTy :=
  let first : Code (.list InputTy) (.list InputTy) :=
    .comp (.pair .id (.const .nat 0)) Code.listNth
  .pair (.comp first (.comp (.listMap .fst) .listJoin))
    (.comp first (.comp (.listMap .snd) .listSum))

theorem firstMarking_nil : firstMarking.eval [] = ([], 0) := by rfl

theorem firstMarking_cons (x : InputTy.denote) (xs : List InputTy.denote) :
    firstMarking.eval (x :: xs) = x := by
  have h := listNth_eval (τ := InputTy) (l := x :: xs) (i := 0) (by simp)
  change (((Code.listNth.eval (x :: xs, 0)).map Prod.fst).flatten,
    ((Code.listNth.eval (x :: xs, 0)).map Prod.snd).sum) = x
  rw [h]
  simp

theorem firstMarking_mem {l : List InputTy.denote} (h : l ≠ []) : firstMarking.eval l ∈ l := by
  cases l with
  | nil => contradiction
  | cons x xs => rw [firstMarking_cons]; exact List.mem_cons_self

def selectMarking : Code CycleInputTy InputTy := .comp goodMarkings firstMarking

theorem goodMarkings_nonempty {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (hc : GRID_HAMILTONIAN_CYCLE (List.ofFn p)) : goodMarkings.eval (List.ofFn p) ≠ [] := by
  obtain ⟨s, t, h⟩ := exists_good_marking p hc
  have hm : input (p ∘ Equiv.swap 0 s) t ∈ goodMarkings.eval (List.ofFn p) := by
    change _ ∈ (allMarkings.eval (List.ofFn p)).filter markedGuard.eval
    exact List.mem_filter.mpr ⟨(mem_allMarkings p _).mpr ⟨s, t, rfl⟩, h⟩
  intro he
  rw [he] at hm
  contradiction

theorem selectMarking_correct_ofFn {m : Nat} (p : Fin (m + 1) → PointTy.denote) :
    GRID_HAMILTONIAN_CYCLE (List.ofFn p) ↔ MARKED_GRID_CYCLE (selectMarking.eval (List.ofFn p)) := by
  by_cases hn : goodMarkings.eval (List.ofFn p) = []
  · have he : selectMarking.eval (List.ofFn p) = ([], 0) := by
      change firstMarking.eval (goodMarkings.eval (List.ofFn p)) = _
      rw [hn, firstMarking_nil]
    rw [he]
    exact iff_of_false (fun hc => goodMarkings_nonempty p hc hn)
      (fun hc => empty_not_grid_cycle (marked_implies_grid_cycle hc))
  · have hm := firstMarking_mem hn
    change selectMarking.eval (List.ofFn p) ∈
      (allMarkings.eval (List.ofFn p)).filter markedGuard.eval at hm
    obtain ⟨hm, hg⟩ := List.mem_filter.mp hm
    obtain ⟨s, t, he⟩ := (mem_allMarkings p _).mp hm
    rw [he] at hg ⊢
    constructor
    · intro hc
      apply marked_of_guard_of_grid_cycle hg
      exact (grid_cycle_reindex p (Equiv.swap 0 s)).mpr hc
    · intro hc
      exact (grid_cycle_reindex p (Equiv.swap 0 s)).mp (marked_implies_grid_cycle hc)

theorem selectMarking_correct (l : CycleInputTy.denote) :
    GRID_HAMILTONIAN_CYCLE l ↔ MARKED_GRID_CYCLE (selectMarking.eval l) := by
  cases l with
  | nil =>
    have he : selectMarking.eval [] = ([], 0) := rfl
    rw [he]
    exact iff_of_false empty_not_grid_cycle
      (fun h => empty_not_grid_cycle (marked_implies_grid_cycle h))
  | cons q qs =>
    simpa only [List.ofFn_get] using selectMarking_correct_ofFn (m := qs.length) (q :: qs).get

def certifiedSelectMarking : CertifiedReduction GRID_HAMILTONIAN_CYCLE MARKED_GRID_CYCLE where
  code := selectMarking
  correct := selectMarking_correct

def certifiedGridCycleToPath : CertifiedReduction GRID_HAMILTONIAN_CYCLE GRID_HAMILTONIAN_PATH :=
  certifiedSelectMarking.comp certifiedMarkedCycleToPath

end GridHardness
