/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.DecisionProblems
import CliffordFrontier.CliffordVerifier
import CliffordFrontier.SynthesisBound

/-!
# Membership

NP membership for the tableau decision problems with binary thresholds.
-/

public section

namespace CliffordFrontier

open CliffordComplexity Cslib.Complexity
open CliffordSynthesis (CNOTOnly)
open CliffordSynthesis.MatrixCompiler

/-- The block-diagonal Clifford synthesis language admits a polynomial-time verifier. -/
theorem clifford_mem_NP : cliffordSynthesis ∈ NP encSynthesisInput :=
  clifford_mem_NP_of_quadratic_synthesis clifford_at_quadratic_threshold

/-- The CNOT-only synthesis language admits a polynomial-time verifier. -/
theorem cnotOnly_mem_NP : cnotOnlySynthesis ∈ NP encSynthesisInput :=
  cnotOnly_mem_NP_of_quadratic_bound cnot_only_at_quadratic_threshold

end CliffordFrontier
