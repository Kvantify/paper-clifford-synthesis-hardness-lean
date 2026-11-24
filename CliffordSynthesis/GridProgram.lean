/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GridAdequacy
public import CliffordSynthesis.Encoding

/-!
# Grid Program

Correctness of the polynomial-time grid-to-tableau program, including failure of
the reduction to accept malformed source instances.

## References

* [FugledeJorgensen2026]
* [LiGuan2026]
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis.GridCompiler
open CliffordComplexity
open MatrixCompiler

 theorem noOutput_eq : noOutput = encode NoInstance.fanout 1 := by decide

 theorem noOutput_rejects : ¬Accepts noOutput := by
  rw [noOutput_eq]
  unfold Accepts
  rw [decode_encode _ _ (by decide) (by decide)]
  exact NoInstance.fanout_no_instance

/-- Correctness of the compiled dense-output program on every labelled grid
instance, including disconnected inputs and signed binary coordinates. -/
theorem reduce_correct {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (hp : Function.Injective (decoded ∘ p)) (last : Fin (m + 1)) :
    Accepts (reduce.eval (input p last)) ↔
      ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk 0 last, w.IsHamiltonian := by
  by_cases hw : BoundedGrid.InWindow (decoded ∘ p)
  · have ht := (windowTest_eval p last).mpr hw
    change Accepts (if windowTest.eval (input p last) then
      MatrixCompiler.compile.eval (template.eval (input p last)) else noOutput) ↔ _
    rw [ite_eq_left ht, template_eval, compile_correct (BoundedGrid.vertex (decoded ∘ p) last)
      (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m))
      (EncodedTarget.recorderCount m + m)]
    change Circuit.SynthesizesWithin (EncodedTarget.instanceTableau (BoundedGrid.vertex (decoded ∘ p)) last)
      (EncodedTarget.recorderCount m + m) ↔ _
    rw [CliffordSynthesis.Reduction.synthesis_iff_hamiltonian _
      (BoundedGrid.vertex_injective _ hw hp) (BoundedGrid.vertex_zero _), BoundedGrid.graph_eq _ hw]
  · have ht : windowTest.eval (input p last) ≠ true := fun h => hw ((windowTest_eval p last).mp h)
    change Accepts (if windowTest.eval (input p last) then
      MatrixCompiler.compile.eval (template.eval (input p last)) else noOutput) ↔ _
    rw [ite_eq_right ht]
    exact iff_of_false noOutput_rejects (fun ⟨w, h⟩ => hw (BoundedGrid.hamiltonian_inWindow _ last w h))

end CliffordSynthesis.GridCompiler
