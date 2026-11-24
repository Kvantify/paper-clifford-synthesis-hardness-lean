/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedProblem
import CliffordSynthesis.GeneralReduction
import CliffordSynthesis.SignedProjection

/-!
# Grid reductions to weighted signed Clifford synthesis

The signed reduction sets generator signs to zero and multiplies the original CNOT budget
by the fixed positive cost of a two-qubit gate.

## Main results

* `grid_to_signed` and `grid_to_structured_signed` are the polynomial-time reductions to
  the full and structured signed decision languages in [FugledeJorgensen2026].
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordComplexity CliffordSynthesis
open CliffordSynthesis.MatrixCompiler CliffordSynthesis.GridCompiler

-- The reduction is used through its correctness theorem. Keep its program folded.
attribute [local irreducible] gridToClifford

private def signless (out : SynthesisInput) : SignedCircuit.Tableau (decode out).qubits :=
  ⟨(decode out).tableau, fun _ => false⟩

private theorem tableau_eq {n : Nat} {a b : SignedCircuit.Tableau n}
    (hl : a.linear = b.linear) (hs : a.sign = b.sign) : a = b := by
  cases a
  cases b
  cases hl
  cases hs
  rfl

private theorem zeroSigns_decode (b : Nat) (out : SynthesisInput) :
    signedTableau (withZeroSigns b out) = signless out := by
  have hl : (signedTableau (withZeroSigns b out)).linear = (signless out).linear := by
    apply FreeLayers.tableau_ext
    intro i p
    rcases p with ⟨j, bit⟩
    cases bit <;> rfl
  have hs : (signedTableau (withZeroSigns b out)).sign = (signless out).sign := by
    funext p
    rcases p with ⟨j, bit⟩
    cases bit <;> rfl
  exact tableau_eq hl hs

private theorem signed_on_outputs (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool)
    (x : GridProblems.GridCode.InputTy.denote) :
    withZeroSigns b (gridToClifford.eval x) ∈ signedSynthesis Γ a b freeSwaps ↔
      Accepts (gridToClifford.eval x) := by
  let out := gridToClifford.eval x
  change SignedCircuit.Synthesizes Γ a b freeSwaps (signedTableau (withZeroSigns b out))
    (b * out.2.2) ↔ Accepts out
  rw [zeroSigns_decode]
  change SignedCircuit.Synthesizes (n := (decode out).qubits) Γ a b freeSwaps
    (signless out) (b * out.2.2) ↔ Accepts out
  constructor
  · rintro ⟨gs, _, hc, hlinear, _⟩
    obtain ⟨ss, hsc, hr⟩ := SignedCircuit.forget_signs a b gs
    have hcost : TwoQubit.StepWithSwap.cost ss ≤ out.2.2 :=
      Nat.le_of_mul_le_mul_left (hsc.trans hc) hb
    apply (gateFamilyFreeSwaps_on_outputs Set.univ TwoQubit.all_supportsCNOT x).mp
    refine ⟨ss, ?_, hcost, ?_⟩
    · intro s _
      cases s with
      | swap => trivial
      | gate g => cases g <;> trivial
    · change Circuit.Same (TwoQubit.StepWithSwap.run ss
        (SignedCircuit.identity (decode out).qubits).linear) (decode out).tableau
      rw [hr (SignedCircuit.identity (decode out).qubits)]
      exact hlinear
  · intro h
    have hcnot : CNOTOnly out := (cnotOnly_on_outputs x).mpr h
    obtain ⟨cs, hc, hs⟩ := hcnot
    obtain ⟨hl, hsign⟩ := SignedCircuit.cnots_run cs
    refine ⟨SignedCircuit.cnots cs, SignedCircuit.cnots_allowed Γ freeSwaps hΓ cs, ?_, ?_, ?_⟩
    · exact (SignedCircuit.cnots_cost a b cs).le.trans (Nat.mul_le_mul_left _ hc)
    · change Circuit.Same (SignedCircuit.run (SignedCircuit.cnots cs)
        (SignedCircuit.identity (decode out).qubits)).linear (decode out).tableau
      rwa [hl]
    · intro p
      exact congrFun hsign p

/-- Specified-endpoint grid Hamiltonian path reduces to weighted signed synthesis. -/
theorem grid_to_signed (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    PolyTimeReducible encGridInput encSignedInput gridHamiltonian
      (signedSynthesis Γ a b freeSwaps) :=
  ⟨_, (gridToClifford.comp (withZeroSignsCode b)).polyTime, fun x =>
    (gridToClifford_correct x).trans (signed_on_outputs Γ a b hb hΓ freeSwaps x).symm⟩

/-- The signed reduction yields three-block targets with zero generator signs. -/
theorem grid_to_structured_signed (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    PolyTimeReducible encGridInput encSignedInput gridHamiltonian
      (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) :=
  ⟨_, (gridToClifford.comp (withZeroSignsCode b)).polyTime, fun x =>
    (gridToClifford_correct x).trans ((signed_on_outputs Γ a b hb hΓ freeSwaps x).symm.trans
      (and_iff_right (show withZeroSigns b (gridToClifford.eval x) ∈ structuredSignedTargets b from
        ⟨_, gridToClifford_restrictions x, rfl⟩)).symm)⟩

end CliffordFrontier
