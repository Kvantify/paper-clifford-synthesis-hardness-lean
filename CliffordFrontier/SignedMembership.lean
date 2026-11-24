/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedSimulationCorrectness
public import CliffordFrontier.SignedSimulationTime
public import CliffordSynthesis.FullSynthesisSignedCertificates

/-!
# Signed Membership

NP membership for the fixed-weight signed tableau decision problems.
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordSynthesis Turing.MultiTapeTM

namespace SignedVerifier

private def width (out : SignedInput) : Nat := (decodeFull out.1).qubits
private def budget (out : SignedInput) : Nat := (decodeFull out.1).threshold

private theorem width_bound (out : SignedInput) : width out ≤ (encSignedInput out).length :=
  (FullVerifier.width_bound out.1).trans
    (length_le_encPair_left encFullTableauInput encSigns out)

private abbrev encVerifierInput := encPair encSignedInput encWitness

private noncomputable def check (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (swaps : Bool)
    (x : SignedInput × List RawStep) : Bool :=
  let n := width x.1
  let result := x.2.foldl (fun state gate => applyRawStep (state, gate)) (initial n)
  costWithin a b (budget x.1, x.2) && x.2.all (validStep Γ swaps n) &&
    compare n result (target x.1)

private theorem check_encoded_iff (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (swaps : Bool)
    (out : SignedInput) (gs : List (SignedCircuit.Step (width out)))
    (ha : ∀ g ∈ gs, g.allowed Γ swaps) :
    check Γ a b swaps (out, gs.map encodeStep) = true ↔
      SignedCircuit.cost a b gs ≤ budget out ∧
      SignedCircuit.Same (SignedCircuit.run gs (SignedCircuit.identity (width out))) (signedTableau out) := by
  have hv : (gs.map encodeStep).all (validStep Γ swaps (width out)) = true := by
    apply List.all_eq_true.mpr
    intro raw hraw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hraw
    exact valid_encodeStep Γ swaps g (ha g hg)
  have hr := run_raw_steps (initial (width out)) (FullVerifier.identity_square _) gs
  have ht : asTableau (width out) (target out) = signedTableau out := target_correct out
  simp only [check, Bool.and_eq_true, hv, and_true,
    costWithin_encoded_iff, compare_correct, hr, initial_correct, ht]

private theorem check_sound (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (swaps : Bool)
    (out : SignedInput) (raw : List RawStep) (h : check Γ a b swaps (out, raw) = true) :
    out ∈ signedSynthesis Γ a b swaps := by
  have hv : raw.all (validStep Γ swaps (width out)) = true := by
    simp only [check, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨gs, ha, rfl⟩ := decode_steps Γ swaps raw hv
  obtain ⟨hc, hs⟩ := (check_encoded_iff Γ a b swaps out gs ha).mp h
  exact ⟨gs, ha, hc, hs⟩

private theorem bool_list_size (xs : List Bool) :
    (encList encBool xs).length ≤ 3 * xs.length := by
  simpa [encBool_apply, Nat.mul_comm] using
    (length_encList_le encBool xs (b := 1) (by simp [encBool_apply]))

private theorem state_size {n : Nat} {s : SignedState} (hp : FullVerifier.PackedSquare n s.1)
    (hx : s.2.1.length = n) (hz : s.2.2.length = n) :
    (encSignedState s).length ≤ 160 * (n + 1) ^ 2 := by
  have hlin := FullVerifier.packed_encoded_size hp
  have hx' := bool_list_size s.2.1
  have hz' := bool_list_size s.2.2
  rw [hx] at hx'
  rw [hz] at hz'
  have hsign : (encSigns s.2).length ≤ 9 * n + 1 := by
    unfold encSigns
    rw [length_encPair]
    omega
  unfold encSignedState
  rw [length_encPair]
  nlinarith

private theorem fold_shape (n : Nat) (gs : List RawStep) (s : SignedState)
    (hp : FullVerifier.PackedSquare n s.1) (hx : s.2.1.length = n) (hz : s.2.2.length = n) :
    let result := gs.foldl (fun state gate => applyRawStep (state, gate)) s
    FullVerifier.PackedSquare n result.1 ∧ result.2.1.length = n ∧ result.2.2.length = n := by
  induction gs generalizing s with
  | nil => exact ⟨hp, hx, hz⟩
  | cons g gs ih =>
    obtain ⟨hx', hz'⟩ := step_sign_lengths n s g hp
    exact ih _ (step_square n s g hp) hx' hz'

private theorem fold_size (x : SignedInput × List RawStep) (i : Nat) :
    (encSignedState ((x.2.take i).foldl (fun state gate => applyRawStep (state, gate))
      (initial (width x.1)))).length ≤ 160 * (width x.1 + 1) ^ 2 := by
  obtain ⟨hp, hx, hz⟩ := fold_shape _ (x.2.take i) (initial (width x.1))
    (FullVerifier.identity_square _) (List.length_replicate ..) (List.length_replicate ..)
  exact state_size hp hx hz

private theorem check_polyTime (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (swaps : Bool) :
    ComputableInPolyTime (check Γ a b swaps) encVerifierInput encBool := by
  let out := ComputableTidilyInPolyTime.fst encSignedInput encWitness
  let witness := ComputableTidilyInPolyTime.snd encSignedInput encWitness
  have n := (ComputableTidilyInPolyTime.length_list (encList encBool)).comp out.fst'.fst'.fst'
  have run := ComputableTidilyInPolyTime.foldl'
    (step := fun state gate => applyRawStep (state, gate))
    witness (initial_polyTime.tidy.comp n) applyRawStep_polyTime.tidy
    (B := fun x => 160 * (width x.1 + 1) ^ 2)
    (.of_forall_le 160 2 fun x =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right ((width_bound x.1).trans
          (length_le_encPair_left encSignedInput encWitness x)) 1) 2))
    (fun x i _ => fold_size x i)
  have valid := ComputableTidilyInPolyTime.allWith (validStep_polyTime Γ swaps).tidy n witness
  have costOk := (costWithin_polyTime a b).tidy.comp (out.fst'.snd'.snd'.prod witness)
  have same := compare_polyTime.tidy.comp (n.prod (run.prod (target_polyTime.tidy.comp out)))
  exact ((costOk.bool_and' valid).bool_and' same).computableInPolyTime

end SignedVerifier

open SignedVerifier in
theorem signed_mem_NP (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (swaps : Bool) :
    signedSynthesis Γ a b swaps ∈ NP encSignedInput := by
  let p : Polynomial Nat := Polynomial.C (4 * (a + b) + 2) * (Polynomial.X + 1) ^ 4 *
    (525000 * (Polynomial.X + 1))
  apply mem_NP_of_check (p := p) decoder (check_polyTime Γ a b swaps)
  · exact check_sound Γ a b swaps
  · intro out hout
    have accepted : SignedCircuit.Synthesizes Γ a b swaps (signedTableau out) (budget out) := hout
    obtain ⟨gs, ha, hc, hl, hs⟩ :=
      SignedCircuit.bounded_certificate Γ a b hb swaps hΓ (signedTableau out) (budget out) accepted
    refine ⟨gs.map encodeStep, (check_encoded_iff Γ a b swaps out gs ha).mpr ⟨hc, hs⟩, ?_⟩
    have hn := Nat.add_le_add_right (width_bound out) 1
    have hl' := hl.trans (SignedCircuit.certificateLength_le a b (width out))
    simp only [p, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    exact (encode_word_size gs).trans (Nat.mul_le_mul
      (hl'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 4)))
      (Nat.mul_le_mul_left _ hn))

end CliffordFrontier
