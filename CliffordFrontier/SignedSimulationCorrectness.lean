/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedSimulation
public import CliffordSynthesis.FullSynthesisSignedLocals

/-!
# Signed Simulation Correctness

The packed simulator preserves the linear and sign components of the signed tableau.
-/

public section

namespace CliffordFrontier.SignedVerifier

open CliffordSynthesis

theorem initial_correct (n : Nat) : asTableau n (initial n) = SignedCircuit.identity n := by
  apply SignedCircuit.tableau_ext (identityPacked_correct n)
  rintro ⟨i, flag⟩
  cases flag <;> simp [asTableau, initial, SignedCircuit.identity]

theorem target_correct (out : SignedInput) :
    asTableau (decodeFull out.1).qubits (target out) = signedTableau out := by
  apply SignedCircuit.tableau_ext (FullVerifier.target_correct out.1)
  intro p
  rfl

theorem compare_correct (n : Nat) (s t : SignedState) :
    compare n s t = true ↔ SignedCircuit.Same (asTableau n s) (asTableau n t) := by
  simp only [compare, Bool.and_eq_true, FullVerifier.comparePacked_correct, compareSigns_iff,
    SignedCircuit.Same]
  constructor
  · rintro ⟨⟨hlinear, hx⟩, hz⟩
    refine ⟨hlinear, ?_⟩
    rintro ⟨i, flag⟩
    cases flag
    · exact hx i.val i.isLt
    · exact hz i.val i.isLt
  · rintro ⟨hlinear, hsign⟩
    exact ⟨⟨hlinear, fun i hi => hsign (⟨i, hi⟩, false)⟩, fun i hi => hsign (⟨i, hi⟩, true)⟩

theorem step_square (n : Nat) (s : SignedState) (g : RawStep)
    (h : FullVerifier.PackedSquare n s.1) :
    FullVerifier.PackedSquare n (applyRawStep (s, g)).1 :=
  FullVerifier.applyPairBlocks_square n s.1 (indices g) (swapping g) (matrix g) h

theorem step_sign_lengths (n : Nat) (s : SignedState) (g : RawStep)
    (h : FullVerifier.PackedSquare n s.1) :
    (applyRawStep (s, g)).2.1.length = n ∧ (applyRawStep (s, g)).2.2.length = n := by
  simp [applyRawStep, signStep, h.1.1, h.2.2.1.1]

private theorem frame_of_fin (f : Fin 6) : frame f.val = f :=
  Fin.ext (Nat.mod_eq_of_lt f.isLt)

private theorem frameMatrix_action_fn (f : Fin 6) :
    TwoQubit.action (frameMatrix f) = TwoQubit.localAction f 0 :=
  funext (frameMatrix_action f)

private theorem update_frame {n : Nat} (a : Circuit.Tableau n) (q : Fin n) (f : Fin 6) :
    TwoQubit.update q q (TwoQubit.localAction f 0) a =
      FreeLayers.applyFrames (Function.update (fun _ => 0) q f) a := by
  apply FreeLayers.tableau_ext
  intro i p
  by_cases h : i = q <;>
    simp [FreeLayers.pair, FreeLayers.applyFrames, TwoQubit.update, TwoQubit.read,
      TwoQubit.localAction, h, FreeLayers.act_zero]

private theorem linearStep_correct {n : Nat} (s : PackedTableau)
    (h : FullVerifier.PackedSquare n s) (g : SignedCircuit.Step n) :
    asPackedTableau n (linearStep s (encodeStep g)) =
      (SignedCircuit.applyStep g ⟨asPackedTableau n s, fun _ => false⟩).linear := by
  cases g with
  | single i f =>
      change asPackedTableau n
        (FullVerifier.applyPairBlocks (s.1, (i.val, i.val), false, frameMatrix (frame f.1.val)),
         FullVerifier.applyPairBlocks (s.2, (i.val, i.val), false, frameMatrix (frame f.1.val))) = _
      rw [frame_of_fin, FullVerifier.applyPairBlocks_correct s h.1.1 h.2.2.1.1 i i]
      change TwoQubit.update i i (TwoQubit.action (frameMatrix f.1)) (asPackedTableau n s) = _
      rw [frameMatrix_action_fn]
      exact update_frame (asPackedTableau n s) i f.1
  | two c t hct m =>
      change asPackedTableau n
        (FullVerifier.applyPairBlocks (s.1, (c.val, t.val), false, BitVec.ofNat 16 m.1.val.toNat),
         FullVerifier.applyPairBlocks (s.2, (c.val, t.val), false, BitVec.ofNat 16 m.1.val.toNat)) = _
      have hm : BitVec.ofNat 16 m.1.val.toNat = m.1.val := by simp
      rw [hm]
      exact FullVerifier.applyPairBlocks_correct s h.1.1 h.2.2.1.1 c t false m.1.val
  | swap c t =>
      change asPackedTableau n
        (FullVerifier.applyPairBlocks (s.1, (c.val, t.val), true, 0),
         FullVerifier.applyPairBlocks (s.2, (c.val, t.val), true, 0)) =
          FreeSwaps.reorder (Equiv.swap c t) (asPackedTableau n s)
      exact (FullVerifier.applyPairBlocks_correct s h.1.1 h.2.2.1.1 c t true 0).trans
        (FullVerifier.update_swap _ c t)

private theorem signStep_get {n : Nat} (s : Blocks × List Bool) (h : s.1.1.length = n)
    (g : RawStep) (j : Fin n) :
    (signStep s g)[j.val]?.getD false = signAfter s g j.val := by
  simp [signStep, h, j.isLt]

private theorem step_correct {n : Nat} (s : SignedState)
    (h : FullVerifier.PackedSquare n s.1) (g : SignedCircuit.Step n) :
    asTableau n (applyRawStep (s, encodeStep g)) = SignedCircuit.applyStep g (asTableau n s) := by
  apply SignedCircuit.tableau_ext
  · change asPackedTableau n (linearStep s.1 (encodeStep g)) = _
    rw [linearStep_correct s.1 h g]
    cases g <;> rfl
  · rintro ⟨j, flag⟩
    cases g with
    | single i f =>
        cases flag <;>
          simp [asTableau, applyRawStep, signStep_get, h.1.1, h.2.2.1.1,
            signAfter, encodeStep, matrix, frame_of_fin, frameMatrix_action_fn, swapping,
            SignedCircuit.applyStep, FreeLayers.pair, asPackedTableau]
    | two c t hct m =>
        have hm : BitVec.ofNat 16 m.1.val.toNat = m.1.val := by simp
        cases flag <;>
          simp [asTableau, applyRawStep, signStep_get, h.1.1, h.2.2.1.1,
            signAfter, encodeStep, matrix, hm, swapping, SignedCircuit.applyStep,
            TwoQubit.read, asPackedTableau]
    | swap c t =>
        cases flag <;>
          simp [asTableau, applyRawStep, signStep_get, h.1.1, h.2.2.1.1,
            signAfter, encodeStep, swapping, SignedCircuit.applyStep]

theorem run_raw_steps {n : Nat} (s : SignedState) (h : FullVerifier.PackedSquare n s.1)
    (gs : List (SignedCircuit.Step n)) :
    asTableau n ((gs.map encodeStep).foldl (fun state g => applyRawStep (state, g)) s) =
      SignedCircuit.run gs (asTableau n s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, SignedCircuit.run]
      rw [ih _ (step_square n s (encodeStep g) h), step_correct s h g]

end CliffordFrontier.SignedVerifier
