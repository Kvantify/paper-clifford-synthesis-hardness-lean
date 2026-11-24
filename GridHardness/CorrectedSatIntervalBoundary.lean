/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalHorizontal

/-!
# Corrected SAT Interval Boundary

Transport the true, variable-side boundary of the active XOR through
actual interval requests. Together with the retained false interface, these
are the two complementary boundary identities needed by a drawing induction.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.Boundary
open XorLineRegistry XorLineSchedule XorLine

variable {n : Nat}

/-- A vertex outside the eight vertices of the active XOR. This includes
the original variable-chain neighbors and previously retained cells. -/
abbrev Outside (s : IntervalState n) (a : Fin n) :=
  {v : s.Vertex // v ∉ Set.range (s.positioned.registry.xors.embed a)}

def transport (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (o : Outside s a) :
    Outside (s.cross a line height hc) a :=
  ⟨.inl ⟨.inl o.val, Bundle.old_not_in_sourceMarker _ _
    (fun k he => o.property ⟨k,he⟩)⟩, by
      rintro ⟨k,hk⟩
      rw [Horizontal.latest_active] at hk
      cases hk⟩

theorem transport_injective (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) : Function.Injective (transport s a line height hc) := by
  intro o p he
  apply Subtype.ext
  exact Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj (congrArg Subtype.val he)))

theorem true_incoming (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (o : Outside s a) :
    (s.cross a line height hc).adj (transport s a line height hc o).val
      ((s.cross a line height hc).positioned.registry.xors.embed a 3) ↔
      s.adj o.val (s.positioned.registry.xors.embed a 3) := by
  rw [Horizontal.latest_active]
  change (∃ p, Subdivision.Adj s.adj _ _ (.inl o.val)
    (sourceMarker (s.positioned.registry.xors.embed a) (Source.inputPort 4 p)) ∧
      inputPort 4 (.inl true) = inputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,he⟩
    have he' : p = .inl true := (inputPort_injective 4 he).symm
    subst p
    exact hp.1
  · intro he
    refine ⟨.inl true, ⟨he,?_⟩, rfl⟩
    rintro ⟨i,_,hi⟩
    exact s.positioned.registry.xor_ne_target a (s.select line height hc).val i 3 hi

theorem true_outgoing (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (o : Outside s a) :
    (s.cross a line height hc).adj
      ((s.cross a line height hc).positioned.registry.xors.embed a 0)
      (transport s a line height hc o).val ↔
      s.adj (s.positioned.registry.xors.embed a 0) o.val := by
  rw [Horizontal.latest_active]
  change (∃ p, Subdivision.Adj s.adj _ _
    (sourceMarker (s.positioned.registry.xors.embed a) (Source.outputPort 4 p))
    (.inl o.val) ∧ outputPort 4 (.inl true) = outputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,he⟩
    have he' : p = .inl true := (outputPort_injective 4 he).symm
    subst p
    exact hp.1
  · intro he
    refine ⟨.inl true, ⟨he,?_⟩, rfl⟩
    rintro ⟨i,hi,_⟩
    exact s.positioned.registry.xor_ne_source a (s.select line height hc).val i 0 hi

/-- Carry a fixed outside vertex through the same recursion as the actual
row executor, retaining its proof of separation from the active XOR. -/
def carryRequests (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j ∈ requests, s.Covered j height) (o : Outside s a) :
    Outside (s.crossRequests a height requests hn hc) a :=
  match requests with
  | [] => o
  | i::is => carryRequests (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (transport s a i height (hc i (by simp)) o)

theorem carryRequests_injective (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j ∈ requests, s.Covered j height) :
    Function.Injective (carryRequests s a height requests hn hc) := by
  induction requests generalizing s with
  | nil => exact fun _ _ h => h
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) _ _).comp
      (transport_injective s a i height (hc i (by simp)))

theorem requests_true_incoming (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j ∈ requests, s.Covered j height) (o : Outside s a) :
    (s.crossRequests a height requests hn hc).adj
      (carryRequests s a height requests hn hc o).val
      ((s.crossRequests a height requests hn hc).positioned.registry.xors.embed a 3) ↔
      s.adj o.val (s.positioned.registry.xors.embed a 3) := by
  induction requests generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) _ _
      (transport s a i height (hc i (by simp)) o)).trans
      (true_incoming s a i height (hc i (by simp)) o)

theorem requests_true_outgoing (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j ∈ requests, s.Covered j height) (o : Outside s a) :
    (s.crossRequests a height requests hn hc).adj
      ((s.crossRequests a height requests hn hc).positioned.registry.xors.embed a 0)
      (carryRequests s a height requests hn hc o).val ↔
      s.adj (s.positioned.registry.xors.embed a 0) o.val := by
  induction requests generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) _ _
      (transport s a i height (hc i (by simp)) o)).trans
      (true_outgoing s a i height (hc i (by simp)) o)

end GridHardness.CorrectedSatInterval.Boundary
