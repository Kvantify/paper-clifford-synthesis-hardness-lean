/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedProblem
public import CliffordFrontier.StructuredMembership
public import CslibFrontier.Computability.Complexity.Classes.NP.Closure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Structured Signed Membership

A polynomial verifier for the image of the three-block targets under the signed
embedding with zero generator signs and scaled budgets.
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordComplexity CliffordSynthesis.MatrixCompiler Turing.MultiTapeTM

private def unsignedBlocks : Code SignedInputTy (Ty.pair MatrixTy MatrixTy) :=
  .pair (.comp .fst (.comp .fst .fst)) (.comp .fst (.comp .snd (.comp .fst .snd)))

private def budget : Code SignedInputTy .nat := .comp .fst (.comp .snd .snd)

private def sourceInstance (b : Nat) (x : SignedInput) : SynthesisInput :=
  (x.1.1.1, x.1.2.1.2, x.1.2.2 / b)

private theorem sourceInstance_polyTime (b : Nat) :
    ComputableInPolyTime (sourceInstance b) encSignedInput encSynthesisInput := by
  have quotient := ComputableInPolyTime.binary_div' budget.polyTime
    (ComputableInPolyTime.const (encIn := encSignedInput) b)
  exact unsignedBlocks.polyTime.fst'.prod (unsignedBlocks.polyTime.snd'.prod quotient)

private instance : DecidableEq SignedInput := encSignedInput.injective.decidableEq

private def checkImage (b : Nat) (x : SignedInput) : Bool :=
  decide (withZeroSigns b (sourceInstance b x) = x)

private theorem checkImage_polyTime (b : Nat) :
    ComputableInPolyTime (checkImage b) encSignedInput encBool := by
  have hs : ComputableInPolyTime (withZeroSigns b) encSynthesisInput encSignedInput := by
    rw [← withZeroSignsCode_eval]
    exact (withZeroSignsCode b).polyTime
  have hid : ComputableInPolyTime id encSignedInput encSignedInput := ComputableInPolyTime.id'
  exact (hs.comp (sourceInstance_polyTime b)).decide_eq' hid

private theorem sourceInstance_withZeroSigns (b : Nat) (hb : 0 < b) (x : SynthesisInput) :
    sourceInstance b (withZeroSigns b x) = x := by
  rcases x with ⟨X, Z, k⟩
  change (X, Z, (b * k) / b) = (X, Z, k)
  rw [Nat.mul_div_cancel_left _ hb]

/-- The signed structured targets have zero signs and a budget scaled by the two-qubit cost. -/
theorem structuredSignedTargets_mem_NP (b : Nat) (hb : 0 < b) :
    structuredSignedTargets b ∈ NP encSignedInput := by
  have hpre : (sourceInstance b ⁻¹' structuredTargets) ∈ NP encSignedInput :=
    PolyTimeReducible.mem_NP ⟨sourceInstance b, sourceInstance_polyTime b, fun _ => Iff.rfl⟩
      structuredTargets_mem_NP
  apply mem_NP_of_guard (checkImage_polyTime b) hpre
  intro x
  constructor
  · rintro ⟨out, hout, rfl⟩
    simp only [Set.mem_preimage, sourceInstance_withZeroSigns b hb, checkImage, decide_true]
    exact ⟨trivial, hout⟩
  · rintro ⟨hc, hs⟩
    exact ⟨sourceInstance b x, hs, of_decide_eq_true hc⟩

end CliffordFrontier
