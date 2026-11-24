/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GateProblems
public import CliffordSynthesis.CNOTOnly

/-!
# Swaps Reduction

The same certified polynomial program reduces to synthesis with both free
one-qubit Cliffords and free SWAP gates.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis

open CliffordComplexity
open MatrixCompiler GridProblems.GridCode GridCompiler

theorem accepts_implies_freeSwaps {out : OutputTy.denote} (h : Accepts out) : WithFreeSwaps out :=
  FreeSwaps.of_circuit _ _ h

theorem noOutput_freeSwaps : ¬WithFreeSwaps noOutput := by
  rw [noOutput_eq]
  unfold WithFreeSwaps
  rw [decode_encode _ _ (by decide) (by decide)]
  exact FreeSwaps.fanout_no_instance

theorem freeSwaps_reduce_sound {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (hp : Function.Injective (decoded ∘ p)) (last : Fin (m + 1))
    (h : WithFreeSwaps (CliffordSynthesis.GridCompiler.reduce.eval (input p last))) :
    ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk 0 last, w.IsHamiltonian := by
  by_cases hw : BoundedGrid.InWindow (decoded ∘ p)
  · have ht := (windowTest_eval p last).mpr hw
    change WithFreeSwaps (if windowTest.eval (input p last) then
      MatrixCompiler.compile.eval (template.eval (input p last)) else noOutput) at h
    rw [ite_eq_left ht, template_eval, compile_encode (BoundedGrid.vertex (decoded ∘ p) last)
      (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m))] at h
    unfold WithFreeSwaps at h
    rw [decode_encode _ _ (fun _ _ => rfl) (fun _ _ => rfl)] at h
    have hh := FreeSwaps.target_soundness
      (EncodedTarget.physicalLabel (2 * m + 2 * m) (EncodedTarget.recorderCount m))
      (BoundedGrid.vertex (decoded ∘ p)) (BoundedGrid.vertex_injective _ hw hp)
      (BoundedGrid.vertex_zero _) (EncodedTarget.copies m) last h
    rwa [BoundedGrid.graph_eq _ hw] at hh
  · have ht : windowTest.eval (input p last) ≠ true := fun h => hw ((windowTest_eval p last).mp h)
    change WithFreeSwaps (if windowTest.eval (input p last) then
      MatrixCompiler.compile.eval (template.eval (input p last)) else noOutput) at h
    rw [ite_eq_right ht] at h
    exact False.elim (noOutput_freeSwaps h)

/-- Even free SWAPs do not improve the answer on any output of the total map,
including its constant rejection branches. -/
theorem freeSwaps_on_outputs (x : InputTy.denote) :
    WithFreeSwaps (gridToClifford.eval x) ↔ Accepts (gridToClifford.eval x) := by
  refine ⟨?_, accepts_implies_freeSwaps⟩
  intro h
  apply (gridToClifford_correct x).mp
  by_cases hv : validCode.eval x = true
  · obtain ⟨m, p, last, rfl, hp⟩ := (validCode_correct x).mp hv
    change WithFreeSwaps (if validCode.eval (input p last) then CliffordSynthesis.GridCompiler.reduce.eval (input p last) else noOutput) at h
    rw [ite_eq_left hv] at h
    exact ⟨m, p, last, rfl, hp, freeSwaps_reduce_sound p hp last h⟩
  · change WithFreeSwaps (if validCode.eval x then CliffordSynthesis.GridCompiler.reduce.eval x else noOutput) at h
    rw [ite_eq_right hv] at h
    exact False.elim (noOutput_freeSwaps h)

def certifiedGridToFreeSwaps : CertifiedReduction GRID_HAMILTONIAN_PATH WithFreeSwaps where
  code := gridToClifford
  correct x := (gridToClifford_correct x).trans (freeSwaps_on_outputs x).symm

end CliffordSynthesis
