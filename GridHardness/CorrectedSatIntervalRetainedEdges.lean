/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalFalseEdges
public import GridHardness.CorrectedSatIntervalPermutationWirePlacement
public import GridHardness.SatCrossingRetirementSides

/-!
# Corrected SAT Interval Retained Edges

Internal edges of a retained crossing survive every later update.
The invariant is directional: a fresh row input is protected as a source,
and a fresh row output as a target. The opposite directions participate
in registered bundles and are deliberately not asserted to be protected.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.RetainedEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev RetainedVertex := SatCrossingHorizontal.RetainedVertex

/-- The row input has outgoing protection, and the row output has incoming
protection. All retained XOR vertices have protection in both directions. -/
def Direction (incoming : Bool) (v : RetainedVertex) : Prop :=
  ∀ i b, v.val=row i b → b=incoming

instance (incoming : Bool) (v : RetainedVertex) : Decidable (Direction incoming v) := by
  unfold Direction
  infer_instance

theorem input_direction (i : Fin 4) :
    Direction false ⟨row i false,trivial⟩ := by
  intro j b he
  exact (Prod.mk.inj (Sum.inr.inj he)).2.symm

theorem output_direction (i : Fin 4) :
    Direction true ⟨row i true,trivial⟩ := by
  intro j b he
  exact (Prod.mk.inj (Sum.inr.inj he)).2.symm

theorem internal_directions : ∀ u v : RetainedVertex, Adj 4 u.val v.val →
    Direction false u ∧ Direction true v := by decide +kernel

private theorem fresh_endpoint_opposite :
    ∀ (side : Bool) (i : Fin 4) (incoming : Bool) (t : Slot),
      BundleSegments.endpointTag BundleSegments.towardTrue (side,(i,incoming))=.inr t →
      t.2≠incoming := by decide +kernel

variable {n : Nat}

/-- The protection is established from the actual split registry, including
both newly registered residual intervals. -/
theorem cross_safe (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (incoming : Bool) (v : RetainedVertex)
    (hv : Direction incoming v) :
    TrueEdges.Safe (s.cross a line height hc) incoming (.inr v.val) := by
  constructor
  · intro b k he
    by_cases hba : b=a
    · subst b
      rw [Horizontal.latest_active] at he
      exact False.elim (SatCrossingHorizontal.retained_ne_zero v k (Sum.inr.inj he))
    · change s.positioned.registry.crossXor a (s.select line height hc).val b k=_ at he
      rw [Registry.crossXor_other _ _ _ _ hba] at he
      cases he
  · intro b i
    change endpoint (s.positioned.registry.splitBundle a (s.select line height hc).val
      BundleSegments.towardTrue b) (i,incoming)≠_
    cases b with
    | inl b =>
      change endpoint (s.positioned.registry.crossBundle a (s.select line height hc).val b.val)
        (i,incoming)≠_
      rw [Registry.crossBundle_other _ _ _ _ b.property]
      intro he
      cases he
    | inr side =>
      change endpoint (BundleSegments.side (s.positioned.registry.bundles (s.select line height hc).val)
        (s.positioned.registry.xors.embed a) _ _
        (BundleSegments.selected BundleSegments.towardTrue side)) (i,incoming)≠_
      rw [BundleSegments.side_endpoint_tag]
      cases he : BundleSegments.endpointTag BundleSegments.towardTrue (side,(i,incoming)) with
      | inl t => intro h; cases h
      | inr t =>
        intro h
        exact fresh_endpoint_opposite side i incoming t he
          (hv t.1 t.2 (Sum.inr.inj h).symm)

theorem rowFresh_safe (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (incoming : Bool) (v : RetainedVertex)
    (hv : Direction incoming v) :
    TrueEdges.Safe (s.crossRequests a height rs hn hc) incoming
      (rowFresh s a height rs hn hc t v) := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht : t.val=0
    · simp only [rowFresh,dite_eq_left ht]
      exact TrueEdges.row_safe _ _ _ _ _ _ incoming _ (cross_safe s a i height _ incoming v hv)
    · simp only [rowFresh,dite_eq_right ht]
      exact ih _ _ _ _

theorem rowFresh_adj (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (u v : RetainedVertex)
    (hu : Direction false u) (hv : Direction true v) :
    (s.crossRequests a height rs hn hc).adj (rowFresh s a height rs hn hc t u)
      (rowFresh s a height rs hn hc t v) ↔ Adj 4 u.val v.val := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht : t.val=0
    · simp only [rowFresh,dite_eq_left ht]
      exact TrueEdges.row_adj _ _ _ _ _ _ _ _
        (cross_safe s a i height _ false u hu) (cross_safe s a i height _ true v hv)
    · simp only [rowFresh,dite_eq_right ht]
      exact ih _ _ _ _

theorem runFresh_safe (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (t : Fin (moveCount height n j)) (incoming : Bool) (v : RetainedVertex),
      Direction incoming v →
      TrueEdges.Safe (runState height hinj hpos n j s h) incoming
        (runFresh height hinj hpos n j s h t v) := by
  induction n with
  | zero => intro j s h t; exact Fin.elim0 t
  | succ n ih =>
    intro j s h t incoming v hv
    by_cases ht : t.val<(requests height j).length
    · simp only [runFresh,dite_eq_left ht]
      exact TrueEdges.run_safe height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) incoming _
        (TrueEdges.retire_safe _ _ _ _ incoming _
          (rowFresh_safe s 0 (height j) (requests height j) (requests_nodup height j)
            h.requests_covered ⟨t.val,ht⟩ incoming v hv))
    · simp only [runFresh,dite_eq_right ht]
      exact ih _ _ _ _ incoming v hv

/-- Exact same-cell adjacency through the whole run for protected
directions. This also rules out extra edges between these candidates. -/
theorem runFresh_adj (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (t : Fin (moveCount height n j)) (u v : RetainedVertex),
      Direction false u → Direction true v →
      ((runState height hinj hpos n j s h).adj (runFresh height hinj hpos n j s h t u)
        (runFresh height hinj hpos n j s h t v) ↔ Adj 4 u.val v.val) := by
  induction n with
  | zero => intro j s h t; exact Fin.elim0 t
  | succ n ih =>
    intro j s h t u v hu hv
    by_cases ht : t.val<(requests height j).length
    · simp only [runFresh,dite_eq_left ht]
      exact (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (TrueEdges.retire_safe _ _ _ _ false _
          (rowFresh_safe s 0 (height j) (requests height j) (requests_nodup height j)
            h.requests_covered ⟨t.val,ht⟩ false u hu))
        (TrueEdges.retire_safe _ _ _ _ true _
          (rowFresh_safe s 0 (height j) (requests height j) (requests_nodup height j)
            h.requests_covered ⟨t.val,ht⟩ true v hv))).trans
        (rowFresh_adj s 0 (height j) (requests height j) (requests_nodup height j)
          h.requests_covered ⟨t.val,ht⟩ u v hu hv)
    · simp only [runFresh,dite_eq_right ht]
      exact ih _ _ _ _ u v hu hv

/-- Every internal edge whose endpoints are retained survives, without
requiring the caller to supply the directional facts. -/
theorem runFresh_edge (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n j : Nat) (s : IntervalState n) (h : Ready s height j)
    (t : Fin (moveCount height n j)) (u v : RetainedVertex) (he : Adj 4 u.val v.val) :
    (runState height hinj hpos n j s h).adj (runFresh height hinj hpos n j s h t u)
      (runFresh height hinj hpos n j s h t v) :=
  (runFresh_adj height hinj hpos n j s h t u v
    (internal_directions u v he).1 (internal_directions u v he).2).mpr he

/-- A vertex outside all live XORs may be a bundle endpoint. Such vertices
can lose an edge to subdivision, but cannot acquire an edge to each other. -/
def Apart (s : IntervalState n) (v : s.Vertex) : Prop :=
  ∀ a k,s.positioned.registry.xors.embed a k≠v

def outside (s : IntervalState n) (a : Fin n) (v : s.Vertex) (hv : Apart s v) :
    Boundary.Outside s a := ⟨v,by rintro ⟨k,hk⟩; exact hv a k hk⟩

theorem cross_apart (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : s.Vertex) (hv : Apart s v) :
    Apart (s.cross a line height hc) (crossLift s a line height hc v) := by
  intro b k he
  by_cases hba : b=a
  · subst b
    rw [←crossLift_current_xor] at he
    exact hv a k (CoreEdges.crossLift_injective s a line height hc he)
  · rw [←crossLift_other_xor s a b hba line height hc] at he
    exact hv b k (CoreEdges.crossLift_injective s a line height hc he)

theorem cross_adj_back (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (u v : s.Vertex) (hu : Apart s u) (hv : Apart s v) :
    (s.cross a line height hc).adj (crossLift s a line height hc u)
      (crossLift s a line height hc v) → s.adj u v := by
  have hlu := crossLift_survivor s a line height hc (outside s a u hu)
  have hlv := crossLift_survivor s a line height hc (outside s a v hv)
  change crossLift s a line height hc u=_ at hlu
  change crossLift s a line height hc v=_ at hlv
  rw [hlu,hlv]
  exact And.left

theorem retire_apart (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (v : s.Vertex) (hv : Apart s v) :
    Apart (s.retire line upper hfresh) v := fun a k => hv a.succ k

theorem row_apart (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (v : s.Vertex) (hv : Apart s v) :
    Apart (s.crossRequests a height rs hn hc) (rowLift s a height rs hn hc v) := by
  induction rs generalizing s with
  | nil => exact hv
  | cons i is ih =>
    exact ih _ _ _ _ (cross_apart s a i height _ v hv)

theorem row_adj_back (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (u v : s.Vertex) (hu : Apart s u) (hv : Apart s v) :
    (s.crossRequests a height rs hn hc).adj (rowLift s a height rs hn hc u)
      (rowLift s a height rs hn hc v) → s.adj u v := by
  induction rs generalizing s with
  | nil => exact id
  | cons i is ih =>
    intro he
    exact cross_adj_back s a i height _ u v hu hv
      (ih _ _ _ _ _ (cross_apart s a i height _ u hu) (cross_apart s a i height _ v hv) he)

theorem next_apart (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (v : s.Vertex) (hv : Apart s v) :
    Apart (next s height j h) (nextLift s height j h v) :=
  retire_apart _ _ _ _ _
    (row_apart s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered v hv)

theorem run_adj_back (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (u v : s.Vertex),
      Apart s u → Apart s v →
      (runState height hinj hpos n j s h).adj (runLift height hinj hpos n j s h u)
        (runLift height hinj hpos n j s h v) → s.adj u v := by
  induction n with
  | zero => intro j s h u v hu hv he; exact he
  | succ n ih =>
    intro j s h u v hu hv he
    exact row_adj_back s 0 (height j) (requests height j) (requests_nodup height j)
      h.requests_covered u v hu hv
      (ih _ _ _ _ _ (next_apart s height j h u hu) (next_apart s height j h v hv) he)

theorem fresh_apart (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : RetainedVertex) :
    Apart (s.cross a line height hc) (.inr v.val) := by
  intro b k he
  by_cases hba : b=a
  · subst b
    rw [Horizontal.latest_active] at he
    exact SatCrossingHorizontal.retained_ne_zero v k (Sum.inr.inj he)
  · change s.positioned.registry.crossXor a (s.select line height hc).val b k=_ at he
    rw [Registry.crossXor_other _ _ _ _ hba] at he
    cases he

theorem rowFresh_apart (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (v : RetainedVertex) :
    Apart (s.crossRequests a height rs hn hc) (rowFresh s a height rs hn hc t v) := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht : t.val=0
    · simp only [rowFresh,dite_eq_left ht]
      exact row_apart _ _ _ _ _ _ _ (fresh_apart s a i height _ v)
    · simp only [rowFresh,dite_eq_right ht]
      exact ih _ _ _ _

theorem rowFresh_adj_back (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (u v : RetainedVertex) :
    (s.crossRequests a height rs hn hc).adj (rowFresh s a height rs hn hc t u)
      (rowFresh s a height rs hn hc t v) → Adj 4 u.val v.val := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    by_cases ht : t.val=0
    · simp only [rowFresh,dite_eq_left ht]
      exact row_adj_back _ _ _ _ _ _ _ _
        (fresh_apart s a i height _ u) (fresh_apart s a i height _ v)
    · simp only [rowFresh,dite_eq_right ht]
      exact ih _ _ _ _

theorem runFresh_adj_back (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (t : Fin (moveCount height n j)) (u v : RetainedVertex),
      (runState height hinj hpos n j s h).adj (runFresh height hinj hpos n j s h t u)
        (runFresh height hinj hpos n j s h t v) → Adj 4 u.val v.val := by
  induction n with
  | zero => intro j s h t; exact Fin.elim0 t
  | succ n ih =>
    intro j s h t u v
    by_cases ht : t.val<(requests height j).length
    · simp only [runFresh,dite_eq_left ht]
      intro he
      exact rowFresh_adj_back s 0 (height j) (requests height j) (requests_nodup height j)
        h.requests_covered ⟨t.val,ht⟩ u v
        (run_adj_back height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h) _ _
          (retire_apart _ _ _ _ _
            (rowFresh_apart s 0 (height j) (requests height j) (requests_nodup height j)
              h.requests_covered ⟨t.val,ht⟩ u))
          (retire_apart _ _ _ _ _
            (rowFresh_apart s 0 (height j) (requests height j) (requests_nodup height j)
              h.requests_covered ⟨t.val,ht⟩ v)) he)
    · simp only [runFresh,dite_eq_right ht]
      exact ih _ _ _ _ u v

/-- Complete same-cell adjacency, including candidates with unsafe row
directions: those directions contain no internal edge and gain none. -/
theorem runFresh_adj_iff (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n j : Nat) (s : IntervalState n) (h : Ready s height j)
    (t : Fin (moveCount height n j)) (u v : RetainedVertex) :
    (runState height hinj hpos n j s h).adj (runFresh height hinj hpos n j s h t u)
      (runFresh height hinj hpos n j s h t v) ↔ Adj 4 u.val v.val :=
  ⟨runFresh_adj_back height hinj hpos n j s h t u v,
    runFresh_edge height hinj hpos n j s h t u v⟩

open PlanarSatAssembly
variable {m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

theorem permutation_adj (c : WireCrossingSchedule.Cell p) (u v : RetainedVertex)
    (hu : Direction false u) (hv : Direction true v) :
    (PermutationGraph.graph φ p).adj (PermutationWirePlacement.fresh φ p c u)
      (PermutationWirePlacement.fresh φ p c v) ↔ Adj 4 u.val v.val :=
  runFresh_adj (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
    (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    ((PermutationWirePlacement.crossingEquiv p).symm c) u v hu hv

theorem permutation_edge (c : WireCrossingSchedule.Cell p) (u v : RetainedVertex)
    (he : Adj 4 u.val v.val) :
    (PermutationGraph.graph φ p).adj (PermutationWirePlacement.fresh φ p c u)
      (PermutationWirePlacement.fresh φ p c v) :=
  (permutation_adj φ p c u v (internal_directions u v he).1
    (internal_directions u v he).2).mpr he

theorem permutation_adj_iff (c : WireCrossingSchedule.Cell p) (u v : RetainedVertex) :
    (PermutationGraph.graph φ p).adj (PermutationWirePlacement.fresh φ p c u)
      (PermutationWirePlacement.fresh φ p c v) ↔ Adj 4 u.val v.val :=
  runFresh_adj_iff (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
    (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    ((PermutationWirePlacement.crossingEquiv p).symm c) u v

end GridHardness.CorrectedSatInterval.RetainedEdges
