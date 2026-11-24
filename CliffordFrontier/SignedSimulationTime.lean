/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedSimulation

/-!
# Signed Simulation Time

Polynomial-time certificates for packed signed-tableau simulation, initialization,
target extraction and equality testing.
-/

@[expose] public section

namespace CliffordFrontier.SignedVerifier

open Turing.MultiTapeTM CliffordSynthesis
open FullVerifier (encBits4 encMat)

local instance : Finite TwoQubit.Matrix :=
  Finite.of_injective BitVec.toFin (fun _ _ h => BitVec.eq_of_toNat_eq (congrArg Fin.val h))

private theorem matrix_polyTime : ComputableInPolyTime matrix encRawStep encMat := by
  let encFrame : Fin 6 ↪ List Bool :=
    ⟨fun i => encUnary i.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩
  have getFrame : ComputableInPolyTime frame encUnary encFrame :=
    ComputableInPolyTime.unary_finMod (by decide) encFrame
  have getMatrix : ComputableInPolyTime frameMatrix encFrame encMat :=
    ComputableInPolyTime.of_finite _
  let raw := ComputableInPolyTime.id' (encIn := encRawStep)
  have key := raw.snd'.snd'.fst'
  exact raw.fst'.fst'.ite (FullVerifier.matrix_polyTime.comp key) (getMatrix.comp (getFrame.comp key))

private theorem swapping_polyTime : ComputableInPolyTime swapping encRawStep encBool := by
  let raw := ComputableInPolyTime.id' (encIn := encRawStep)
  exact raw.fst'.fst'.bool_and' raw.fst'.snd'

private theorem indices_polyTime : ComputableInPolyTime indices encRawStep encCNOTIndices := by
  let raw := ComputableInPolyTime.id' (encIn := encRawStep)
  have pair := raw.snd'.fst'
  exact raw.fst'.fst'.ite pair (pair.fst'.prod pair.fst')

private theorem linearStep_polyTime :
    ComputableInPolyTime (fun p : PackedTableau × RawStep => linearStep p.1 p.2)
      (encPair encPackedTableau encRawStep) encPackedTableau := by
  let data := ComputableInPolyTime.fst encPackedTableau encRawStep
  let gate := ComputableInPolyTime.snd encPackedTableau encRawStep
  have params := (indices_polyTime.prod (swapping_polyTime.prod matrix_polyTime)).comp gate
  exact (FullVerifier.applyPairBlocks_polyTime.comp (data.fst'.prod params)).prod
    (FullVerifier.applyPairBlocks_polyTime.comp (data.snd'.prod params))

private abbrev encSignStepInput := encPair (encPair encBlocks (encList encBool)) encRawStep

private theorem signStep_polyTime :
    ComputableInPolyTime (fun p : (Blocks × List Bool) × RawStep => signStep p.1 p.2)
      encSignStepInput (encList encBool) := by
  let input := ComputableInPolyTime.fst encSignStepInput encUnary
  let col := ComputableInPolyTime.snd encSignStepInput encUnary
  let blocks := input.fst'.fst'
  let gate := input.snd'
  let pair := gate.snd'.fst'
  have previous := readSign_polyTime.comp (input.fst'.snd'.prod col)
  have xc := entry_polyTime blocks.fst' pair.fst' col
  have zc := entry_polyTime blocks.snd' pair.fst' col
  have xt := gate.fst'.fst'.bool_and' (entry_polyTime blocks.fst' pair.snd' col)
  have zt := gate.fst'.fst'.bool_and' (entry_polyTime blocks.snd' pair.snd' col)
  have flip : ComputableInPolyTime
      (fun q : TwoQubit.Matrix × TwoQubit.Bits × TwoQubit.Bits =>
        SignedCircuit.signChange (TwoQubit.action q.1) q.2.1 q.2.2)
      (encPair encMat (encPair encBits4 encBits4)) encBool := ComputableInPolyTime.of_finite _
  have delta := flip.comp ((matrix_polyTime.comp gate).prod
    (gate.snd'.snd'.snd'.prod (xc.prod (zc.prod (xt.prod zt)))))
  have update := (swapping_polyTime.comp gate).ite previous
    (ComputableInPolyTime.bool_xor.comp (previous.prod delta))
  have data := ComputableInPolyTime.fst (encPair encBlocks (encList encBool)) encRawStep
  have width := (ComputableInPolyTime.length_list (encList encBool)).comp data.fst'.fst'
  exact tabulateSigns_polyTime width update

theorem applyRawStep_polyTime :
    ComputableInPolyTime applyRawStep (encPair encSignedState encRawStep) encSignedState := by
  let state := ComputableInPolyTime.fst encSignedState encRawStep
  let gate := ComputableInPolyTime.snd encSignedState encRawStep
  have linear := linearStep_polyTime.comp (state.fst'.prod gate)
  have sx := signStep_polyTime.comp ((state.fst'.fst'.prod state.snd'.fst').prod gate)
  have sz := signStep_polyTime.comp ((state.fst'.snd'.prod state.snd'.snd').prod gate)
  exact linear.prod (sx.prod sz)

theorem initial_polyTime : ComputableInPolyTime initial encUnary encSignedState := by
  have zeros : ComputableInPolyTime (fun n : Nat => List.replicate n false) encUnary (encList encBool) :=
    ComputableInPolyTime.replicate ComputableInPolyTime.id' (ComputableInPolyTime.const false)
  exact identityPacked_polyTime.prod (zeros.prod zeros)

theorem target_polyTime : ComputableInPolyTime target encSignedInput encSignedState := by
  let out := ComputableInPolyTime.fst encFullTableauInput encSigns
  let signs := ComputableInPolyTime.snd encFullTableauInput encSigns
  exact (FullVerifier.targetPacked_polyTime.comp out).prod signs

theorem compare_polyTime :
    ComputableInPolyTime (fun p : Nat × SignedState × SignedState => compare p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encSignedState encSignedState)) encBool := by
  let width := ComputableInPolyTime.fst encUnary (encPair encSignedState encSignedState)
  let states := ComputableInPolyTime.snd encUnary (encPair encSignedState encSignedState)
  let a := states.fst'
  let b := states.snd'
  have eqLinear := comparePacked_polyTime.comp (width.prod (a.fst'.prod b.fst'))
  have eqX := compareSigns_polyTime.comp (width.prod (a.snd'.fst'.prod b.snd'.fst'))
  have eqZ := compareSigns_polyTime.comp (width.prod (a.snd'.snd'.prod b.snd'.snd'))
  exact (eqLinear.bool_and' eqX).bool_and' eqZ

end CliffordFrontier.SignedVerifier
