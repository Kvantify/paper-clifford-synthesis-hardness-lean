/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.TwoQubitNormal
public import CliffordSynthesis.TwoQubitSemantics
public import CliffordSynthesis.TwoQubitSymplectic

/-!
# Two Qubit Circuits

Circuits over all two-qubit Clifford symplectic maps. The paid gates are
specified independently by their 4×4 matrices, not by a decomposition.
-/

@[expose] public section

namespace CliffordSynthesis.TwoQubit

abbrev Gate := {p : Matrix // valid p = true}

inductive Step (n : Nat) where
  | H (i : Fin n)
  | S (i : Fin n)
  | two (c t : Fin n) (distinct : c ≠ t) (gate : Gate)

variable {n : Nat}

def applyStep : Step n → Circuit.Tableau n → Circuit.Tableau n
  | .H i => Circuit.hadamard i
  | .S i => Circuit.phase i
  | .two c t _ g => update c t (action g.val)

def paid : Step n → Nat
  | .H _ | .S _ => 0
  | .two _ _ _ _ => 1

def cost : List (Step n) → Nat
  | [] => 0
  | g :: gs => paid g + cost gs

def run : List (Step n) → Circuit.Tableau n → Circuit.Tableau n
  | [], a => a
  | g :: gs, a => run gs (applyStep g a)

theorem cost_append (gs hs : List (Step n)) : cost (gs ++ hs) = cost gs + cost hs := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih => simp [cost, ih, Nat.add_assoc]

theorem run_append (gs hs : List (Step n)) (a : Circuit.Tableau n) :
    run (gs ++ hs) a = run hs (run gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih (applyStep g a)

def Synthesizes (target : Circuit.Tableau n) (k : Nat) : Prop :=
  ∃ gs : List (Step n), cost gs ≤ k ∧ Circuit.Same (run gs (Circuit.identity n)) target

/-- Replace each arbitrary two-qubit gate by its proved finite normal form.
The circuit equality holds on every input tableau. -/
theorem to_freeSwaps (gs : List (Step n)) :
    ∃ ss : List (FreeSwaps.Step n), FreeSwaps.count ss ≤ cost gs ∧
      ∀ a, FreeSwaps.execute ss a = run gs a := by
  induction gs with
  | nil => exact ⟨[], le_rfl, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ss, hc, hr⟩ := ih
    cases g with
    | H i => exact ⟨.gate (.H i) :: ss, by simpa [FreeSwaps.count, Circuit.paid, cost, paid] using hc, fun a => hr (Circuit.hadamard i a)⟩
    | S i => exact ⟨.gate (.S i) :: ss, by simpa [FreeSwaps.count, Circuit.paid, cost, paid] using hc, fun a => hr (Circuit.phase i a)⟩
    | two c t hct g =>
      obtain ⟨f, hf⟩ := normal_form g.val g.property
      refine ⟨normalSteps c t hct f ++ ss, ?_, ?_⟩
      · rw [FreeSwaps.count_append]
        exact Nat.add_le_add (normalSteps_cost c t hct f) hc
      · intro a
        rw [FreeSwaps.execute_append, normalSteps_run, hr]
        change run gs (update c t (normalAction f) a) = run gs (update c t (action g.val) a)
        rw [funext hf]

/-- Two-qubit normalization, including transport of all SWAPs to the output.
L paid arbitrary two-qubit gates yield at most L CNOTs and a final permutation. -/
theorem normalize_circuit (gs : List (Step n)) :
    ∃ p : Equiv.Perm (Fin n), ∃ cs : List (Circuit.Gate n), Circuit.cost cs ≤ cost gs ∧
      ∀ a, run gs a = FreeSwaps.reorder p (Circuit.run cs a) := by
  obtain ⟨ss, hc, hr⟩ := to_freeSwaps gs
  exact ⟨(FreeSwaps.normalize ss).1, (FreeSwaps.normalize ss).2,
    by rwa [FreeSwaps.normalize_cost], fun a => (hr a).symm.trans (FreeSwaps.normalize_run ss a)⟩

theorem synthesis_to_freeSwaps (target : Circuit.Tableau n) (k : Nat)
    (h : Synthesizes target k) : FreeSwaps.Synthesizes target k := by
  obtain ⟨gs, hk, hs⟩ := h
  obtain ⟨ss, hc, hr⟩ := to_freeSwaps gs
  exact ⟨ss, hc.trans hk, by rwa [hr]⟩

/-- Matrix of CNOT in the X₀,Z₀,X₁,Z₁ convention. -/
def cnotGate : Gate := ⟨34209#16, by decide⟩

theorem cnotGate_action : ∀ v : Bits, action cnotGate.val v = cnotAction v := by decide

def ofGate : Circuit.Gate n → Step n
  | .H i => .H i
  | .S i => .S i
  | .CX c t hct => .two c t hct cnotGate

theorem ofGate_apply (g : Circuit.Gate n) (a : Circuit.Tableau n) :
    applyStep (ofGate g) a = Circuit.applyGate g a := by
  cases g with
  | H i => rfl
  | S i => rfl
  | CX c t hct =>
    change update c t (action cnotGate.val) a = Circuit.cnot c t a
    rw [funext cnotGate_action, cnot_update c t hct]

theorem ofGate_cost (gs : List (Circuit.Gate n)) : cost (gs.map ofGate) = Circuit.cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [List.map_cons, cost, ofGate, paid, Circuit.cost, Circuit.paid, ih]

theorem ofGate_run (gs : List (Circuit.Gate n)) (a : Circuit.Tableau n) :
    run (gs.map ofGate) a = Circuit.run gs a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, run, ofGate_apply, ih, Circuit.run]

theorem of_circuit (target : Circuit.Tableau n) (k : Nat) (h : Circuit.SynthesizesWithin target k) :
    Synthesizes target k := by
  obtain ⟨gs, hk, hs⟩ := h
  exact ⟨gs.map ofGate, by rwa [ofGate_cost], by rwa [ofGate_run]⟩

end CliffordSynthesis.TwoQubit
