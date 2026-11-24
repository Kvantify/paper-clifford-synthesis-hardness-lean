/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.FullVerifier
public import CliffordSynthesis.SignedCircuit

/-!
# Signed Witness

Encoded signed gates and polynomial-time validation of a circuit certificate.
-/

public section

namespace CliffordFrontier.SignedVerifier

open CliffordSynthesis CliffordComplexity Turing.MultiTapeTM
open TwoQubit (Bits Matrix)
open FullVerifier (encBits4 encMat matrix_polyTime)

/-- A gate tag, wire indices, a frame or matrix key, and four generator signs. -/
abbrev RawStep := (Bool × Bool) × CNOTIndices × Nat × Bits
/-- The instruction tag encoding shared with the phase-free verifier. -/
abbrev encTag := FullVerifier.encTag
/-- Encode a signed instruction with unary wire indices and matrix key. -/
abbrev encRawStep : RawStep ↪ List Bool :=
  encPair encTag (encPair encCNOTIndices (encPair encUnary encBits4))
/-- Encode a list of raw signed circuit instructions. -/
abbrev encWitness : List RawStep ↪ List Bool := encList encRawStep

/-- Decode a raw signed circuit certificate. -/
@[expose] def decoder : Decoder encWitness :=
  let boolPair := Decoder.pair Decoder.bool Decoder.bool
  let natPair := Decoder.pair Decoder.unary Decoder.unary
  let signs := Decoder.pair Decoder.bool (Decoder.pair Decoder.bool boolPair)
  Decoder.list (Decoder.pair boolPair (Decoder.pair natPair (Decoder.pair Decoder.unary signs)))

/-- Encode a typed signed gate or free SWAP as a raw instruction. -/
@[expose] def encodeStep {n : Nat} : SignedCircuit.Step n → RawStep
  | .single i g => ((false, false), (i.val, 0), g.1.val, (g.2.1, g.2.2, false, false))
  | .two c t _ g => ((true, false), (c.val, t.val), g.1.val.toNat, g.2)
  | .swap c t => ((true, true), (c.val, t.val), 0, (false, false, false, false))

local instance : Finite Matrix :=
  Finite.of_injective BitVec.toFin (fun _ _ h => BitVec.eq_of_toNat_eq (congrArg Fin.val h))

private noncomputable def signedGateAllowed (Γ : Set SignedCircuit.TwoGate) (p : Matrix × Bits) : Bool :=
  if h : TwoQubit.valid p.1 = true then @decide ((⟨p.1, h⟩, p.2) ∈ Γ) (Classical.propDecidable _)
  else false

private theorem signedGateAllowed_iff (Γ : Set SignedCircuit.TwoGate) (m : Matrix) (s : Bits) :
    signedGateAllowed Γ (m, s) = true ↔ ∃ g : TwoQubit.Gate, (g, s) ∈ Γ ∧ g.val = m := by
  classical
  unfold signedGateAllowed
  split
  next h =>
    rw [decide_eq_true_eq]
    constructor
    · intro hg
      exact ⟨⟨m, h⟩, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  next h =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨g, _, rfl⟩
    exact h g.property

/-- Check eligibility, wire bounds, and canonical data for a signed instruction. -/
noncomputable def validStep (Γ : Set SignedCircuit.TwoGate) (swaps : Bool) (n : Nat) (g : RawStep) : Bool :=
  if g.1.1 then
    if g.1.2 then swaps && decide (g.2.1.1 < n ∧ g.2.1.2 < n ∧ g.2.2.1 = 0 ∧
      g.2.2.2 = (false, false, false, false))
    else validIndices n g.2.1 && decide (g.2.2.1 < 2 ^ 16) &&
      signedGateAllowed Γ (BitVec.ofNat 16 g.2.2.1, g.2.2.2)
  else !g.1.2 && decide (g.2.1.1 < n ∧ g.2.1.2 = 0 ∧ g.2.2.1 < 6 ∧
    g.2.2.2.2.2 = (false, false))

theorem validStep_polyTime (Γ : Set SignedCircuit.TwoGate) (swaps : Bool) :
    ComputableInPolyTime (fun p : Nat × RawStep => validStep Γ swaps p.1 p.2)
      (encPair encUnary encRawStep) encBool := by
  have width := ComputableInPolyTime.fst encUnary encRawStep
  have gate := ComputableInPolyTime.snd encUnary encRawStep
  have indices := gate.snd'.fst'
  have key := gate.snd'.snd'.fst'
  have signs := gate.snd'.snd'.snd'
  have matrixBound := ComputableTidilyInPolyTime.unary_lt' key.tidy
    (ComputableTidilyInPolyTime.const (2 ^ 16))
  have localBound := ComputableTidilyInPolyTime.unary_lt' key.tidy
    (ComputableTidilyInPolyTime.const 6)
  have c := ComputableTidilyInPolyTime.unary_lt' indices.fst'.tidy width.tidy
  have t := ComputableTidilyInPolyTime.unary_lt' indices.snd'.tidy width.tidy
  have tZero := indices.snd'.decide_eq' (ComputableInPolyTime.const 0)
  have keyZero := key.decide_eq' (ComputableInPolyTime.const 0)
  have signZero := signs.decide_eq' (ComputableInPolyTime.const (false, false, false, false))
  have trailingZero := signs.snd'.snd'.decide_eq' (ComputableInPolyTime.const (false, false))
  have validTwo := validIndices_polyTime.comp (width.prod indices)
  have allowed : ComputableInPolyTime (signedGateAllowed Γ) (encPair encMat encBits4) encBool :=
    ComputableInPolyTime.of_finite _
  have hMat := allowed.comp ((matrix_polyTime.comp key).prod signs)
  have hSwap := (ComputableInPolyTime.const swaps).bool_and'
    (c.computableInPolyTime.bool_and' (t.computableInPolyTime.bool_and' (keyZero.bool_and' signZero)))
  have hLocal := (ComputableInPolyTime.bool_not.comp gate.fst'.snd').bool_and'
    (c.computableInPolyTime.bool_and' (tZero.bool_and' (localBound.computableInPolyTime.bool_and' trailingZero)))
  have hTwo := (validTwo.bool_and' matrixBound.computableInPolyTime).bool_and' hMat
  refine (gate.fst'.fst'.ite (gate.fst'.snd'.ite hSwap hTwo) hLocal).of_enc_eq ?_
  intro p
  simp [validStep, Function.comp_apply, Bool.decide_and]

theorem valid_encodeStep {n : Nat} (Γ : Set SignedCircuit.TwoGate) (swaps : Bool)
    (g : SignedCircuit.Step n) (h : g.allowed Γ swaps) : validStep Γ swaps n (encodeStep g) = true := by
  cases g with
  | single i g => simp [validStep, encodeStep, i.isLt, g.1.isLt]
  | two c t hct g =>
    have hn : c.val ≠ t.val := fun he => hct (Fin.ext he)
    have hs : signedGateAllowed Γ (g.1.val, g.2) = true :=
      (signedGateAllowed_iff Γ _ _).mpr ⟨g.1, h, rfl⟩
    have hm : g.1.val.toNat < 65536 := g.1.val.isLt
    simp [validStep, encodeStep, validIndices, c.isLt, t.isLt, hn, hs, hm]
  | swap c t =>
    change swaps = true at h
    simpa [validStep, encodeStep, c.isLt, t.isLt] using h

private theorem decode_step {n : Nat} (Γ : Set SignedCircuit.TwoGate) (swaps : Bool)
    (raw : RawStep) (h : validStep Γ swaps n raw = true) :
    ∃ g : SignedCircuit.Step n, g.allowed Γ swaps ∧ encodeStep g = raw := by
  obtain ⟨⟨tag, flag⟩, ⟨c, t⟩, m, s⟩ := raw
  cases tag <;> cases flag
  · obtain ⟨a, b, d, e⟩ := s
    simp [validStep] at h
    obtain ⟨hc, rfl, hm, rfl, rfl⟩ := h
    exact ⟨.single ⟨c, hc⟩ (⟨m, hm⟩, a, b), trivial, rfl⟩
  · simp [validStep] at h
  · change (validIndices n (c, t) && decide (m < 2 ^ 16) &&
      signedGateAllowed Γ (BitVec.ofNat 16 m, s)) = true at h
    simp only [validIndices, Bool.and_eq_true, decide_eq_true_eq, signedGateAllowed_iff] at h
    obtain ⟨⟨⟨hc, ht, hct⟩, hm⟩, g, hg, he⟩ := h
    refine ⟨.two ⟨c, hc⟩ ⟨t, ht⟩ (fun h => hct (congrArg Fin.val h)) (g, s), hg, ?_⟩
    dsimp [encodeStep]
    rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  · simp [validStep, Bool.and_eq_true] at h
    obtain ⟨hs, hc, ht, rfl, rfl⟩ := h
    exact ⟨.swap ⟨c, hc⟩ ⟨t, ht⟩, hs, rfl⟩

theorem decode_steps {n : Nat} (Γ : Set SignedCircuit.TwoGate) (swaps : Bool)
    (raw : List RawStep) (h : raw.all (validStep Γ swaps n) = true) :
    ∃ gs : List (SignedCircuit.Step n), (∀ g ∈ gs, g.allowed Γ swaps) ∧ gs.map encodeStep = raw := by
  induction raw with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons raw rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨g, hg, rfl⟩ := decode_step Γ swaps raw h.1
    obtain ⟨gs, hgs, rfl⟩ := ih h.2
    exact ⟨g :: gs, List.forall_mem_cons.mpr ⟨hg, hgs⟩, rfl⟩

private def isSingle (g : RawStep) := !g.1.1 && !g.1.2

private def isTwo (g : RawStep) := g.1.1 && !g.1.2

/-- Compare the weighted sum of single- and two-qubit gates to the binary budget. -/
def costWithin (a b : Nat) (p : Nat × List RawStep) : Bool :=
  decide (a * p.2.countP isSingle + b * p.2.countP isTwo ≤ p.1)

theorem costWithin_polyTime (a b : Nat) :
    ComputableInPolyTime (costWithin a b) (encPair encNat encWitness) encBool := by
  let input := encPair encNat encWitness
  have budget := ComputableTidilyInPolyTime.fst encNat encWitness
  have word := ComputableTidilyInPolyTime.snd encNat encWitness
  have tag := (ComputableTidilyInPolyTime.snd input encRawStep).fst'
  have testSingle : ComputableTidilyInPolyTime (fun p : Bool × Bool => !p.1 && !p.2) encTag encBool :=
    ComputableTidilyInPolyTime.of_finite _
  have testTwo : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && !p.2) encTag encBool :=
    ComputableTidilyInPolyTime.of_finite _
  have singles := ComputableTidilyInPolyTime.unary_to_binary.comp
    (ComputableTidilyInPolyTime.countPWithInput (test := fun _ g => isSingle g) word (testSingle.comp tag))
  have twos := ComputableTidilyInPolyTime.unary_to_binary.comp
    (ComputableTidilyInPolyTime.countPWithInput (test := fun _ g => isTwo g) word (testTwo.comp tag))
  have aCost := ComputableTidilyInPolyTime.binary_mul.comp
    ((ComputableTidilyInPolyTime.const a).prod singles)
  have bCost := ComputableTidilyInPolyTime.binary_mul.comp
    ((ComputableTidilyInPolyTime.const b).prod twos)
  exact (ComputableTidilyInPolyTime.binary_le.comp
    ((ComputableTidilyInPolyTime.binary_add.comp (aCost.prod bCost)).prod budget)).computableInPolyTime

private theorem cost_encodeStep {n : Nat} (a b : Nat) (gs : List (SignedCircuit.Step n)) :
    a * (gs.map encodeStep).countP isSingle + b * (gs.map encodeStep).countP isTwo =
      SignedCircuit.cost a b gs := by
  induction gs with
  | nil => simp [SignedCircuit.cost]
  | cons g gs ih =>
    cases g <;>
      simp [encodeStep, isSingle, isTwo, SignedCircuit.cost, SignedCircuit.Step.weight, ← ih, Nat.mul_succ] <;>
      omega

theorem costWithin_encoded_iff {n : Nat} (a b budget : Nat) (gs : List (SignedCircuit.Step n)) :
    costWithin a b (budget, gs.map encodeStep) = true ↔ SignedCircuit.cost a b gs ≤ budget := by
  simp only [costWithin, decide_eq_true_eq, cost_encodeStep]

private theorem encodeStep_size {n : Nat} (g : SignedCircuit.Step n) :
    2 * (encRawStep (encodeStep g)).length + 1 ≤ 525000 * (n + 1) := by
  cases g with
  | single i g =>
    have hf := g.1.isLt
    simp [encRawStep, encTag, FullVerifier.encTag, encCNOTIndices, encBits4, encodeStep,
      encBool_apply, encUnary_apply]
    omega
  | two c t hct g =>
    have hm : g.1.val.toNat < 2 ^ 16 := g.1.val.isLt
    simp [encRawStep, encTag, FullVerifier.encTag, encCNOTIndices, encBits4, encodeStep,
      encBool_apply, encUnary_apply]
    omega
  | swap c t =>
    simp [encRawStep, encTag, FullVerifier.encTag, encCNOTIndices, encBits4, encodeStep,
      encBool_apply, encUnary_apply]
    omega

theorem encode_word_size {n : Nat} (gs : List (SignedCircuit.Step n)) :
    (encWitness (gs.map encodeStep)).length ≤ gs.length * (525000 * (n + 1)) := by
  rw [length_encList]
  simp only [List.map_map]
  refine (List.sum_le_length_nsmul _ (525000 * (n + 1)) ?_).trans ?_
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact encodeStep_size g
  · simp

end CliffordFrontier.SignedVerifier
