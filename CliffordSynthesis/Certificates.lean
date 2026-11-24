/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FreeLayers

/-!
# Certificates

Polynomial gate-count certificates despite unlimited free gates and
binary thresholds. Time bounds for an explicit string verifier remain separate.
-/

public section

namespace CliffordSynthesis.Certificates

open Circuit FreeLayers

variable {n : Nat}

/-- All free gates before the first CNOT can be stored in six-valued wire
frames. Each subsequent CNOT contributes at most 3n+1 gates. -/
theorem normalize_head (gs : List (Gate n)) :
    ∃ f : Fin n → Fin 6, ∃ cs : List (Gate n),
      cost cs = cost gs ∧ cs.length ≤ (3 * n + 1) * cost gs ∧
      ∀ a, run gs a = run cs (applyFrames f a) := by
  induction gs with
  | nil => exact ⟨fun _ => 0, [], rfl, by simp, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨f, cs, hcost, hlen, heq⟩ := ih
    cases g with
    | H q =>
      refine ⟨Function.update f q (preH (f q)), cs,
        by simpa only [cost, paid, Nat.zero_add] using hcost,
        by simpa only [cost, paid, Nat.zero_add] using hlen, ?_⟩
      intro a
      change run gs (hadamard q a) = _
      rw [heq, frames_preH]
    | S q =>
      refine ⟨Function.update f q (preS (f q)), cs,
        by simpa only [cost, paid, Nat.zero_add] using hcost,
        by simpa only [cost, paid, Nat.zero_add] using hlen, ?_⟩
      intro a
      change run gs (phase q a) = _
      rw [heq, frames_preS]
    | CX c t hct =>
      refine ⟨fun _ => 0, .CX c t hct :: (layer f ++ cs), ?_, ?_, ?_⟩
      · change 1 + cost (layer f ++ cs) = 1 + cost gs
        rw [cost_append, layer_cost, hcost, Nat.zero_add]
      · have hl := layer_length f
        change (.CX c t hct :: (layer f ++ cs)).length ≤ (3 * n + 1) * (1 + cost gs)
        simp only [List.length_cons, List.length_append, Nat.mul_add, Nat.mul_one]
        omega
      · intro a
        change run gs (cnot c t a) = run (layer f ++ cs) (cnot c t (applyFrames (fun _ => 0) a))
        rw [frames_zero, run_append, layer_run, heq]

/-- Free-layer compression preserves the complete tableau on every input and
the paid cost, and bounds the total number of H/S/CNOT gates. -/
theorem normalize (gs : List (Gate n)) :
    ∃ cs : List (Gate n), cost cs = cost gs ∧
      cs.length ≤ 3 * n * (cost gs + 1) + cost gs ∧ ∀ a, run cs a = run gs a := by
  obtain ⟨f, cs, hcost, hlen, heq⟩ := normalize_head gs
  refine ⟨layer f ++ cs, ?_, ?_, ?_⟩
  · rw [cost_append, layer_cost, Nat.zero_add, hcost]
  · have hl := layer_length f
    rw [List.length_append]
    nlinarith
  · intro a
    rw [run_append, layer_run, heq]

theorem bounded_certificate (target : Tableau n) (k : Nat) (h : SynthesizesWithin target k) :
    ∃ cs : List (Gate n), cost cs ≤ k ∧ cs.length ≤ 3 * n * (k + 1) + k ∧
      Same (run cs (identity n)) target := by
  obtain ⟨gs, hcost, hsame⟩ := h
  obtain ⟨cs, he, hl, hr⟩ := normalize gs
  exact ⟨cs, he.trans_le hcost, hl.trans (by gcongr), by rwa [hr]⟩

/-- Apply a supplied synthesis bound B to cap certificates independently of
a binary-encoded threshold k. The bound premise can come from the external
Clifford-synthesis theorem; compression and threshold handling are proved here. -/
theorem capped_certificate (target : Tableau n) (k B : Nat)
    (hk : SynthesizesWithin target k) (hB : SynthesizesWithin target B) :
    ∃ cs : List (Gate n), cost cs ≤ k ∧ cost cs ≤ B ∧
      cs.length ≤ 3 * n * (B + 1) + B ∧ Same (run cs (identity n)) target := by
  have hmin : SynthesizesWithin target (min k B) := by
    rcases le_total k B with h | h
    · simpa only [min_eq_left h] using hk
    · simpa only [min_eq_right h] using hB
  obtain ⟨cs, hc, hl, hs⟩ := bounded_certificate target (min k B) hmin
  exact ⟨cs, hc.trans (min_le_left _ _), hc.trans (min_le_right _ _),
    hl.trans (by gcongr <;> exact min_le_right _ _), hs⟩

end CliffordSynthesis.Certificates
