/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryIntervalRun

/-!
# Corrected SAT Interval Run

Execute an entire insertion sweep against the two-sided interval registry.
Every requested bundle is found in the current registry; coverage and freshness
are consequences of the sweep invariant, not inputs to individual stages.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval
open XorLineRegistry XorLineSchedule

/-- Cross prior lines in increasing horizontal order. The refreshed section
zero lies on the right of the local crossing drawing, so the active true
(variable-side) endpoint advances towards its own vertical column. -/
def requests (height : Nat → Nat) (j : Nat) : List Nat :=
  (List.range j).filter (fun i => decide (height j < height i))

theorem mem_requests (height : Nat → Nat) (i j : Nat) :
    i ∈ requests height j ↔ i < j ∧ height j < height i := by
  simp [requests]

theorem requests_nodup (height : Nat → Nat) (j : Nat) :
    (requests height j).Nodup := by
  have h : (List.range j).Nodup := List.nodup_range
  exact h.filter _

theorem requests_increasing (height : Nat → Nat) (j : Nat) :
    (requests height j).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem requests_length_le (height : Nat → Nat) (j : Nat) :
    (requests height j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq (by simp)

/-- Future crossing heights are still present, even when their interval has
already been split at other heights. -/
structure Ready {n : Nat} (s : IntervalState n) (height : Nat → Nat) (j : Nat) : Prop where
  bound : ∀ b, (s.positioned.segments b).line < j
  covered : ∀ i k, i < j → j ≤ k → height k < height i → s.Covered i (height k)

theorem Ready.requests_covered {n : Nat} {s : IntervalState n}
    {height : Nat → Nat} {j : Nat} (h : Ready s height j) :
    ∀ i ∈ requests height j, s.Covered i (height j) := by
  intro i hi
  obtain ⟨hij, hheight⟩ := (mem_requests height i j).mp hi
  exact h.covered i j hij le_rfl hheight

def crossed {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) : IntervalState (n+1) :=
  s.crossRequests 0 (height j) (requests height j) (requests_nodup height j)
    h.requests_covered

theorem crossed_bound {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat)
    (j : Nat) (h : Ready s height j) :
    ∀ b, ((crossed s height j h).positioned.segments b).line < j :=
  s.crossRequests_line_bound 0 (height j) _ _ _ j h.bound

def next {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) : IntervalState n :=
  (crossed s height j h).retire j (height j)
    (fun b => Nat.ne_of_lt (crossed_bound s height j h b))

theorem next_ready {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat)
    (hinj : Function.Injective height) (hpos : ∀ i, 0 < height i)
    (j : Nat) (h : Ready s height j) : Ready (next s height j h) height (j+1) := by
  constructor
  · intro b
    cases b with
    | none => change j < j+1; omega
    | some b =>
      change ((crossed s height j h).positioned.segments b).line < j+1
      exact (crossed_bound s height j h b).trans (by omega)
  · intro i k hij hjk hheight
    rw [next, IntervalState.retire_coverage]
    by_cases he : i = j
    · subst i
      exact Or.inl ⟨rfl, hpos k, hheight⟩
    · apply Or.inr
      apply (s.crossRequests_coverage 0 (height j) _ _ _ i (height k) ?_).mpr
      · exact h.covered i k (by omega) (by omega) hheight
      · exact Or.inr (fun hhe => by have := hinj hhe; omega)

theorem next_correct {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat)
    (j : Nat) (h : Ready s height j) :
    PathCover.Hamiltonian s.adj ↔ PathCover.Hamiltonian (next s height j h).adj :=
  s.crossRequests_correct 0 (height j) _ _ _

theorem next_vertex_count {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat)
    (j : Nat) (h : Ready s height j) :
    Nat.card (next s height j h).Vertex =
      Nat.card s.Vertex + 40 * (requests height j).length :=
  s.crossRequests_vertex_count 0 (height j) _ _ _

theorem next_enum_length_le {n : Nat} (s : IntervalState (n +1)) (height : Nat → Nat)
    (j : Nat) (h : Ready s height j) :
    (next s height j h).enum.length ≤ s.enum.length + 2*(requests height j).length+1 := by
  rw [next, IntervalState.retire_enum_length]
  have hb := s.crossRequests_enum_length_le 0 (height j)
    (requests height j) (requests_nodup height j) h.requests_covered
  change (crossed s height j h).enum.length ≤ _ at hb
  omega

/-- Retain the final registry as well as the graph, so its working-data size
can be bounded. The graph-facing interface below is just a projection. -/
def runState (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) : (n j : Nat) →
    (s : IntervalState n) → Ready s height j → IntervalState 0
  | 0, _, s, _ => s
  | n+1, j, s, h => runState height hinj hpos n (j+1) (next s height j h)
      (next_ready s height hinj hpos j h)

def run (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n j : Nat) (s : IntervalState n)
    (h : Ready s height j) : FiniteGraph :=
  (runState height hinj hpos n j s h).toFiniteGraph

def moveCount (height : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, j => (requests height j).length + moveCount height n (j+1)

theorem run_correct (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ j (s : IntervalState n)
    (h : Ready s height j), PathCover.Hamiltonian s.adj ↔
      PathCover.Hamiltonian (run height hinj hpos n j s h).adj := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro j s h
    exact (next_correct s height j h).trans (ih (j+1) _ _)

theorem run_vertex_count (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ j (s : IntervalState n)
    (h : Ready s height j),
    Nat.card (run height hinj hpos n j s h).Vertex =
      Nat.card s.Vertex + 40 * moveCount height n j := by
  induction n with
  | zero => intros; simp [run, runState, moveCount]
  | succ n ih =>
    intro j s h
    change Nat.card (run height hinj hpos n (j+1) (next s height j h) _).Vertex = _
    rw [ih, next_vertex_count, moveCount]
    omega

theorem runState_enum_length_le (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ j (s : IntervalState n)
    (h : Ready s height j),
    (runState height hinj hpos n j s h).enum.length ≤
      s.enum.length+n+2*moveCount height n j := by
  induction n with
  | zero => intros; simp [runState, moveCount]
  | succ n ih =>
    intro j s h
    have ht := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
    have hh := next_enum_length_le s height j h
    change (runState height hinj hpos n (j+1) (next s height j h) _).enum.length ≤ _
    rw [moveCount]
    omega

theorem moveCount_le (height : Nat → Nat) (n : Nat) :
    ∀ j, moveCount height n j ≤ n * (j+n) := by
  induction n with
  | zero => intro j; simp [moveCount]
  | succ n ih =>
    intro j
    have htail := ih (j+1)
    have hhead := requests_length_le height j
    rw [moveCount]
    nlinarith

end GridHardness.CorrectedSatInterval
