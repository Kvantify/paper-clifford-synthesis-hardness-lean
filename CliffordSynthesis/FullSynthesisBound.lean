/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FullSynthesisPivot

/-!
# Full Synthesis Bound

A quadratic synthesis bound for phase-free Clifford tableaux.
-/

@[expose] public section

namespace CliffordSynthesis.Circuit

open FreeLayers (pair tableau_ext)

variable {n : Nat}

private def tail (a : Tableau (n + 1)) : Tableau n where
  x i p := a.x i.succ (p.1.succ, p.2)
  z i p := a.z i.succ (p.1.succ, p.2)

private def pad (a : Tableau n) : Tableau (n + 1) where
  x i p := Fin.cases (decide (p.1 = 0) && !p.2)
    (fun j => Fin.cases false (fun k => a.x j (k, p.2)) p.1) i
  z i p := Fin.cases (decide (p.1 = 0) && p.2)
    (fun j => Fin.cases false (fun k => a.z j (k, p.2)) p.1) i

private theorem zero_ne_succ (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ :=
  (Fin.succ_ne_zero i).symm

private theorem pad_identity (n : Nat) : pad (identity n) = identity (n + 1) := by
  apply tableau_ext
  rintro i ⟨j, b⟩
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [pad, pair, identity, zero_ne_succ, Fin.succ_ne_zero]

private theorem split_eq_pad (a : Tableau (n + 1)) (ha : ColumnsSymplectic a)
    (hx : ∀ i, pair a i (0, false) = (decide (i = 0), false))
    (hz : ∀ i, pair a i (0, true) = (false, decide (i = 0))) : a = pad (tail a) := by
  apply tableau_ext
  rintro i ⟨j, b⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · cases b
    · rw [hx]
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [pad, pair, Fin.succ_ne_zero]
    · rw [hz]
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [pad, pair, Fin.succ_ne_zero]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa [pad, pair, Fin.succ_ne_zero] using cleared_head_zero ha hx hz j b
    · simp [pad, tail, pair]

private theorem columnsSymplectic_tail {a : Tableau (n + 1)} (ha : ColumnsSymplectic a)
    (hx : ∀ i, pair a i (0, false) = (decide (i = 0), false))
    (hz : ∀ i, pair a i (0, true) = (false, decide (i = 0))) :
    ColumnsSymplectic (tail a) := by
  rintro ⟨i, b⟩ ⟨j, c⟩
  have hp := ha (i.succ, b) (j.succ, c)
  unfold columnPairing at hp ⊢
  rw [Fin.sum_univ_succ, cleared_head_zero ha hx hz i b] at hp
  rw [show wirePairing (false, false) (pair a 0 (j.succ, c)) = 0 by
    simp [wirePairing, show LocalChart.bit false = 0 from rfl], zero_add] at hp
  simpa only [tail, pair, Fin.succ_inj] using hp

private def liftGate : Gate n → Gate (n + 1)
  | .H i => .H i.succ
  | .S i => .S i.succ
  | .CX i j hij => .CX i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

private theorem paid_liftGate (g : Gate n) : paid (liftGate g) = paid g := by cases g <;> rfl

private theorem cost_lift (gs : List (Gate n)) : cost (gs.map liftGate) = cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [cost, paid_liftGate, ih]

private theorem applyGate_pad (g : Gate n) (a : Tableau n) :
    applyGate (liftGate g) (pad a) = pad (applyGate g a) := by
  apply tableau_ext
  rintro i ⟨j, b⟩
  cases g <;> refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [pad, pair, applyGate, liftGate, hadamard, phase, cnot, zero_ne_succ]

private theorem run_pad (gs : List (Gate n)) (a : Tableau n) :
    run (gs.map liftGate) (pad a) = pad (run gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [run, applyGate_pad, ih]

private theorem applyGate_twice (g : Gate n) (a : Tableau n) :
    applyGate g (applyGate g a) = a := by
  have h : Same (applyGate g (applyGate g a)) a := by
    cases g with
    | H q => exact hadamard_involutive q a
    | S q => exact phase_involutive q a
    | CX c t hct => exact cnot_involutive c t hct a
  exact tableau_ext fun i p => Prod.ext (h i p).1 (h i p).2

private theorem run_reverse_run (gs : List (Gate n)) (a : Tableau n) :
    run gs.reverse (run gs a) = a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.reverse_cons, run_append, run, ih, applyGate_twice]

private theorem cost_reverse (gs : List (Gate n)) : cost gs.reverse = cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp [List.reverse_cons, cost_append, cost, ih, Nat.add_comm]

/-- A symplectic tableau admits a circuit with at most this many CNOT gates. -/
def fullSynthesisCap (n : Nat) : Nat := n ^ 2

private theorem reduce_to_identity (a : Tableau n) (h : ColumnsSymplectic a) :
    ∃ gs : List (Gate n), cost gs ≤ fullSynthesisCap n ∧ run gs a = identity n := by
  induction n with
  | zero =>
      refine ⟨[], by simp [cost, fullSynthesisCap], ?_⟩
      exact tableau_ext fun i _ => Fin.elim0 i
  | succ n ih =>
      obtain ⟨head, hc, hx, hz⟩ := clear_first_qubit a h
      let b := run head a
      have hb : ColumnsSymplectic b := h.run head
      obtain ⟨rest, hr, he⟩ := ih (tail b) (columnsSymplectic_tail hb hx hz)
      refine ⟨head ++ rest.map liftGate, ?_, ?_⟩
      · rw [cost_append, cost_lift]
        unfold fullSynthesisCap at hr ⊢
        nlinarith
      · rw [run_append]
        change run (rest.map liftGate) b = identity (n + 1)
        rw [split_eq_pad b hb hx hz, run_pad, he, pad_identity]

theorem full_synthesis_bound_of_symplectic (a : Tableau n) (h : ColumnsSymplectic a) :
    SynthesizesWithin a (fullSynthesisCap n) := by
  obtain ⟨gs, hc, he⟩ := reduce_to_identity a h
  refine ⟨gs.reverse, by rwa [cost_reverse], ?_⟩
  have hr := run_reverse_run gs a
  rw [he] at hr
  rw [hr]
  intro i p
  exact ⟨rfl, rfl⟩

/-- All phase-free Clifford tableaux reachable from the identity have a quadratic CNOT bound. -/
theorem full_synthesis_bound (target : Tableau n)
    (h : ∃ gs : List (Gate n), Same (run gs (identity n)) target) :
    SynthesizesWithin target (fullSynthesisCap n) := by
  obtain ⟨gs, hg⟩ := h
  have ht : run gs (identity n) = target := tableau_ext fun i p => Prod.ext (hg i p).1 (hg i p).2
  rw [← ht]
  exact full_synthesis_bound_of_symplectic _ ((columnsSymplectic_identity n).run gs)

end CliffordSynthesis.Circuit
