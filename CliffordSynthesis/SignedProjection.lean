/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.SignedCircuit
public import CliffordSynthesis.GeneralReduction

/-!
# Signed Projection

Forgetting generator signs commutes with circuit execution. A CNOT-only circuit
can also be lifted to the signed model with zero signs.
-/

public section

namespace CliffordSynthesis.SignedCircuit

variable {n : Nat}

private theorem run_append (xs ys : List (TwoQubit.StepWithSwap n)) (a : Circuit.Tableau n) :
    TwoQubit.StepWithSwap.run (xs ++ ys) a =
      TwoQubit.StepWithSwap.run ys (TwoQubit.StepWithSwap.run xs a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons g gs ih => cases g <;> exact ih _

private theorem cost_append (xs ys : List (TwoQubit.StepWithSwap n)) :
    TwoQubit.StepWithSwap.cost (xs ++ ys) =
      TwoQubit.StepWithSwap.cost xs + TwoQubit.StepWithSwap.cost ys := by
  induction xs with
  | nil => simp [TwoQubit.StepWithSwap.cost]
  | cons g gs ih => cases g <;> simp [TwoQubit.StepWithSwap.cost, ih, Nat.add_assoc]

private def eraseStep : Step n → List (TwoQubit.StepWithSwap n)
  | .single i g => ((FreeLayers.word i g.1).map TwoQubit.ofGate).map .gate
  | .two i j h g => [.gate (.two i j h g.1)]
  | .swap i j => [.swap i j]

private theorem eraseStep_run (g : Step n) (T : Tableau n) :
    TwoQubit.StepWithSwap.run (eraseStep g) T.linear = (applyStep g T).linear := by
  cases g with
  | single i f =>
    rw [eraseStep, TwoQubit.StepWithSwap.run_gates, TwoQubit.ofGate_run]
    apply FreeLayers.tableau_ext
    intro j p
    rw [FreeLayers.word_run]
    by_cases h : j = i
    · subst j
      simp [applyStep, FreeLayers.applyFrames, FreeLayers.pair]
    · simp [applyStep, FreeLayers.applyFrames, FreeLayers.pair, h, FreeLayers.act_zero]
  | two => rfl
  | swap => rfl

private theorem eraseStep_cost (a b : Nat) (g : Step n) :
    b * TwoQubit.StepWithSwap.cost (eraseStep g) ≤ g.weight a b := by
  cases g with
  | single i f =>
    rw [eraseStep, TwoQubit.StepWithSwap.cost_gates, TwoQubit.ofGate_cost, FreeLayers.word_cost]
    simp [Step.weight]
  | two => simp [eraseStep, TwoQubit.StepWithSwap.cost, TwoQubit.paid, Step.weight]
  | swap => simp [eraseStep, TwoQubit.StepWithSwap.cost, Step.weight]

theorem forget_signs (a b : Nat) (gs : List (Step n)) :
    ∃ ss : List (TwoQubit.StepWithSwap n),
      b * TwoQubit.StepWithSwap.cost ss ≤ cost a b gs ∧
      ∀ T, TwoQubit.StepWithSwap.run ss T.linear = (run gs T).linear := by
  induction gs with
  | nil => exact ⟨[], by simp [TwoQubit.StepWithSwap.cost, cost], fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ss, hc, hr⟩ := ih
    refine ⟨eraseStep g ++ ss, ?_, fun T => ?_⟩
    · rw [cost_append, Nat.mul_add]
      exact Nat.add_le_add (eraseStep_cost a b g) hc
    · rw [run_append, eraseStep_run, hr]
      rfl

private def cnotStep (g : RowExtraction.AddGate n) : Step n :=
  .two g.control g.target g.distinct cnotGate

def cnots (cs : List (RowExtraction.AddGate n)) : List (Step n) := cs.map cnotStep

@[simp] theorem cnots_cost (a b : Nat) (cs : List (RowExtraction.AddGate n)) :
    cost a b (cnots cs) = b * cs.length := by
  induction cs with
  | nil => simp [cnots, cost]
  | cons g gs ih =>
    change b + cost a b (cnots gs) = b * (gs.length + 1)
    rw [ih, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem cnots_allowed (Γ : Set TwoGate) (freeSwaps : Bool) (hΓ : cnotGate ∈ Γ)
    (cs : List (RowExtraction.AddGate n)) :
    ∀ g ∈ cnots cs, g.allowed Γ freeSwaps := by
  intro g hg
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hg
  exact hΓ

private def Separate (a : Circuit.Tableau n) : Prop :=
  ∀ i j, a.x i (j, true) = false ∧ a.z i (j, false) = false

private theorem separate_identity : Separate (Circuit.identity n) := by
  intro i j
  simp [Circuit.identity]

private theorem cnot_separate (c t : Fin n) (T : Circuit.Tableau n) (hT : Separate T) :
    Separate (Circuit.cnot c t T) := by
  intro i j
  simp [Circuit.cnot, (hT i j).1, (hT i j).2, (hT c j).1, (hT t j).2]

private theorem cnot_no_sign : ∀ v : TwoQubit.Bits,
    ((v.1 = false ∧ v.2.2.1 = false) ∨ (v.2.1 = false ∧ v.2.2.2 = false)) →
      signChange TwoQubit.cnotAction (false, false, false, false) v = false := by decide

private theorem cnot_linear (g : RowExtraction.AddGate n) (T : Tableau n) :
    (applyStep (cnotStep g) T).linear = Circuit.applyGate (RowHistory.asGate g) T.linear := by
  change TwoQubit.update g.control g.target (TwoQubit.action TwoQubit.cnotGate.val) T.linear =
    Circuit.cnot g.control g.target T.linear
  rw [funext TwoQubit.cnotGate_action, TwoQubit.cnot_update _ _ g.distinct]

private theorem cnot_sign (g : RowExtraction.AddGate n) (T : Tableau n) (hT : Separate T.linear) :
    (applyStep (cnotStep g) T).sign = T.sign := by
  funext p
  change (T.sign p ^^ signChange (TwoQubit.action TwoQubit.cnotGate.val) (false, false, false, false)
    (TwoQubit.read g.control g.target T.linear p)) = T.sign p
  rw [funext TwoQubit.cnotGate_action, cnot_no_sign]
  · simp
  · rcases p with ⟨j, b⟩
    cases b
    · exact Or.inr ⟨(hT _ j).2, (hT _ j).2⟩
    · exact Or.inl ⟨(hT _ j).1, (hT _ j).1⟩

private theorem cnots_run_from (cs : List (RowExtraction.AddGate n)) (T : Tableau n)
    (hT : Separate T.linear) :
    (run (cnots cs) T).linear = Circuit.run (RowHistory.asCircuit cs) T.linear ∧
      (run (cnots cs) T).sign = T.sign := by
  induction cs generalizing T with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    have hsep : Separate (applyStep (cnotStep g) T).linear := by
      rw [cnot_linear]
      exact cnot_separate _ _ _ hT
    obtain ⟨hl, hs⟩ := ih _ hsep
    constructor
    · change (run (cnots gs) (applyStep (cnotStep g) T)).linear =
        Circuit.run (RowHistory.asCircuit gs) (Circuit.applyGate (RowHistory.asGate g) T.linear)
      rw [hl, cnot_linear]
    · exact hs.trans (cnot_sign g T hT)

theorem cnots_run (cs : List (RowExtraction.AddGate n)) :
    (run (cnots cs) (identity n)).linear = Circuit.run (RowHistory.asCircuit cs) (Circuit.identity n) ∧
      (run (cnots cs) (identity n)).sign = fun _ => false :=
  cnots_run_from cs (identity n) separate_identity

end CliffordSynthesis.SignedCircuit
