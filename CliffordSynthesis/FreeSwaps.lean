/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PermutedRigidity
public import CliffordSynthesis.FreeLayers
public import CliffordSynthesis.NoInstance

/-!
# Free Swaps

Explicit SWAP semantics and normalization. SWAPs can be moved to the output
by relabelling subsequent gates, preserving the exact number of CNOTs.
-/

@[expose] public section

namespace CliffordSynthesis.FreeSwaps

open Circuit

variable {n : Nat}

def reorder (p : Equiv.Perm (Fin n)) (a : Tableau n) : Tableau n where
  x i := a.x (p i)
  z i := a.z (p i)

def relabel (p : Equiv.Perm (Fin n)) : Gate n → Gate n
  | .H i => .H (p i)
  | .S i => .S (p i)
  | .CX c t h => .CX (p c) (p t) (fun he => h (p.injective he))

@[simp] theorem reorder_one (a : Tableau n) : reorder (Equiv.refl _) a = a := by cases a; rfl

@[simp] theorem reorder_reorder (p q : Equiv.Perm (Fin n)) (a : Tableau n) :
    reorder p (reorder q a) = reorder (p.trans q) a := rfl

theorem gate_reorder (g : Gate n) (p : Equiv.Perm (Fin n)) (a : Tableau n) :
    applyGate g (reorder p a) = reorder p (applyGate (relabel p g) a) := by
  apply FreeLayers.tableau_ext
  intro i j
  cases g <;> simp [FreeLayers.pair, applyGate, relabel, reorder, hadamard, phase, cnot]

theorem run_reorder (gs : List (Gate n)) (p : Equiv.Perm (Fin n)) (a : Tableau n) :
    run gs (reorder p a) = reorder p (run (gs.map (relabel p)) a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp only [run, gate_reorder, ih, List.map_cons]

theorem cost_relabel (gs : List (Gate n)) (p : Equiv.Perm (Fin n)) :
    cost (gs.map (relabel p)) = cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [List.map_cons, cost, relabel, paid, ih]

inductive Step (n : Nat) where
  | gate (g : Gate n)
  | swap (i j : Fin n)

def execute : List (Step n) → Tableau n → Tableau n
  | [], a => a
  | .gate g :: gs, a => execute gs (applyGate g a)
  | .swap i j :: gs, a => execute gs (reorder (Equiv.swap i j) a)

def count : List (Step n) → Nat
  | [] => 0
  | .gate g :: gs => paid g + count gs
  | .swap _ _ :: gs => count gs

theorem execute_append (gs hs : List (Step n)) (a : Tableau n) :
    execute (gs ++ hs) a = execute hs (execute gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => cases g <;> exact ih _

theorem count_append (gs hs : List (Step n)) : count (gs ++ hs) = count gs + count hs := by
  induction gs with
  | nil => simp [count]
  | cons g gs ih => cases g <;> simp [count, ih, Nat.add_assoc]

theorem execute_embed (gs : List (Gate n)) (a : Tableau n) :
    execute (gs.map Step.gate) a = run gs a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih (applyGate g a)

theorem count_embed (gs : List (Gate n)) : count (gs.map Step.gate) = cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => change paid g + count (gs.map Step.gate) = paid g + cost gs; rw [ih]

/-- Return the final permutation and the ordinary H/S/CNOT circuit. -/
def normalize : List (Step n) → Equiv.Perm (Fin n) × List (Gate n)
  | [] => (Equiv.refl _, [])
  | .gate g :: gs => let (p, cs) := normalize gs; (p, g :: cs)
  | .swap i j :: gs => let (p, cs) := normalize gs
    (p.trans (Equiv.swap i j), cs.map (relabel (Equiv.swap i j)))

theorem normalize_run (gs : List (Step n)) (a : Tableau n) :
    execute gs a = reorder (normalize gs).1 (run (normalize gs).2 a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | gate g => exact ih (applyGate g a)
    | swap i j =>
      change execute gs (reorder (Equiv.swap i j) a) = _
      rw [ih, run_reorder]
      rfl

theorem normalize_cost (gs : List (Step n)) : cost (normalize gs).2 = count gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | gate g => change paid g + cost (normalize gs).2 = paid g + count gs; rw [ih]
    | swap i j => exact (cost_relabel _ _).trans ih

def Synthesizes (a : Tableau n) (k : Nat) : Prop :=
  ∃ gs : List (Step n), count gs ≤ k ∧ Same (execute gs (identity n)) a

theorem of_circuit (a : Tableau n) (k : Nat) (h : SynthesizesWithin a k) : Synthesizes a k := by
  obtain ⟨gs, hk, hs⟩ := h
  exact ⟨gs.map Step.gate, by rwa [count_embed], by rwa [execute_embed]⟩

/-- Free SWAPs do not change the answer for any replicated reduction target. -/
theorem target_soundness {d r m : Nat} (label : Target.Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → Planes.F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (last : Fin (m + 1))
    (h : Synthesizes (EncodedTarget.tableau label (vertex last) (ReplicatedTarget.repeated vertex copies)) (r + m)) :
    ∃ p : (HamiltonPath.cubeGraph vertex).Walk 0 last, p.IsHamiltonian := by
  obtain ⟨gs, hk, hs⟩ := h
  apply (PermutedRigidity.permuted_soundness label (normalize gs).1 vertex hv hzero copies
    (normalize gs).2 last _ (by rwa [normalize_cost])).2
  intro i
  rw [← EncodedTarget.tableau_x]
  funext p
  apply congrArg LocalChart.bit
  have hh := (hs i p).1
  simpa only [normalize_run, reorder] using hh

/-- Merely producing the r noninitial recorder outputs already costs r CNOTs,
even when their final locations are arbitrary and SWAPs are free. -/
theorem recorder_lower_bound {d r : Nat} (label : Target.Wire d r ≃ Fin n)
    (t : Fin d → Planes.F) (X : Fin r → Fin d → Planes.F) (k : Nat)
    (h : Synthesizes (EncodedTarget.tableau label t X) k) : r ≤ k := by
  obtain ⟨gs, hk, hs⟩ := h
  have hfinal : ∀ i, (StandardSpace.fieldRows (run (normalize gs).2 (identity n))).x
      ((normalize gs).1 i) = RecorderVectors.embed label (Target.matrix t X (label.symm i)) := by
    intro i
    rw [← EncodedTarget.tableau_x]
    funext p
    apply congrArg LocalChart.bit
    simpa only [normalize_run, reorder] using (hs i p).1
  have hlinear := PermutedTarget.target_linear label (normalize gs).1 (normalize gs).2 t X hfinal
  have hout := PermutedTarget.target_recorder_visible label (normalize gs).1 (normalize gs).2 t X hfinal
  simp only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] at hout
  have hb := BirthOccurrences.recorder_count_le_births (StandardSpace.initialW n) (normalize gs).2
    (StandardSpace.standard n) (fun a => (normalize gs).1 (RecorderVectors.recorder label a))
    ((normalize gs).1.injective.comp (RecorderVectors.recorder_injective label)) (RecorderVectors.output label X) hout
    (fun a => by simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
      RecorderVectors.output_not_initial label X a ((normalize gs).1 (RecorderVectors.recorder label a)))
  have hl := CircuitLedger.actual_linear_birth_bound (normalize gs).2 hlinear
  have hc := normalize_cost gs
  omega

theorem fanout_no_instance : ¬Synthesizes NoInstance.fanout 1 := by
  intro h
  have he : Same NoInstance.fanout
      (EncodedTarget.tableau (EncodedTarget.physicalLabel 0 2) 0 (fun _ => 0)) := by unfold Same; decide
  have ht : Synthesizes (EncodedTarget.tableau (EncodedTarget.physicalLabel 0 2) 0 (fun _ => 0)) 1 := by
    obtain ⟨gs, hk, hs⟩ := h
    exact ⟨gs, hk, fun i p => ⟨(hs i p).1.trans (he i p).1, (hs i p).2.trans (he i p).2⟩⟩
  have hh := recorder_lower_bound (EncodedTarget.physicalLabel 0 2) 0 (fun _ => 0) 1 ht
  omega

end CliffordSynthesis.FreeSwaps
