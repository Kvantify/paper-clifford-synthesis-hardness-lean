/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Certified

/-!
# Restricted

The polynomial reduction lands in the three-block family. Thus
its target is symplectic, A is lower unitriangular, and (A-I)^3 = 0.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis
open CliffordComplexity
open GridProblems.GridCode GridCompiler MatrixCompiler
open Planes (F)

/-- An explicit three-block target, with an arbitrary binary threshold. -/
def ThreeBlock (out : OutputTy.denote) : Prop :=
  ∃ (d r : Nat) (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (k : Nat),
    out = encode (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k

theorem noOutput_threeBlock : ThreeBlock noOutput := by
  refine ⟨0, 2, (fun i => Fin.elim0 i), (fun _ i => Fin.elim0 i), 1, ?_⟩
  decide

theorem gridToClifford_threeBlock (x : InputTy.denote) : ThreeBlock (gridToClifford.eval x) := by
  by_cases hv : validCode.eval x = true
  · obtain ⟨m, p, last, rfl, hp⟩ := (validCode_correct x).mp hv
    change ThreeBlock (if validCode.eval (input p last) then CliffordSynthesis.GridCompiler.reduce.eval (input p last) else noOutput)
    rw [ite_eq_left hv]
    change ThreeBlock (if windowTest.eval (input p last) then
      compile.eval (template.eval (input p last)) else noOutput)
    by_cases hw : windowTest.eval (input p last) = true
    · rw [ite_eq_left hw, template_eval, compile_encode (BoundedGrid.vertex (decoded ∘ p) last)
        (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m))]
      exact ⟨_, _, _, _, _, rfl⟩
    · rw [ite_eq_right hw]
      exact noOutput_threeBlock
  · change ThreeBlock (if validCode.eval x then CliffordSynthesis.GridCompiler.reduce.eval x else noOutput)
    rw [ite_eq_right hv]
    exact noOutput_threeBlock

/-- Every output has a lower unitriangular, cube-nilpotent linear block and
a symplectic lift. -/
theorem gridToClifford_restrictions (x : InputTy.denote) :
    ∃ (d r : Nat) (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (k : Nat),
      gridToClifford.eval x = encode (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k ∧
      (Target.matrix t X - 1) ^ 3 = 0 ∧
      (∀ i, Target.matrix t X i i = 1) ∧
      (∀ i j, Target.position i < Target.position j → Target.matrix t X i j = 0) ∧
      Target.lift t X ∈ Matrix.symplecticGroup (Target.Wire d r) F := by
  obtain ⟨d, r, t, X, k, he⟩ := gridToClifford_threeBlock x
  exact ⟨d, r, t, X, k, he, Target.nilpotent_target t X, Target.diagonal t X,
    Target.lower_triangular t X, Target.lift_symplectic t X⟩

/-- Strengthening the target by its three-block restriction preserves the
same program and its polynomial certificate. -/
def certifiedRestricted : CertifiedReduction GRID_HAMILTONIAN_PATH
    (CliffordComplexity.Problem.restrict Accepts ThreeBlock) where
  code := gridToClifford
  correct x := (gridToClifford_correct x).trans (and_iff_right (gridToClifford_threeBlock x)).symm

end CliffordSynthesis
