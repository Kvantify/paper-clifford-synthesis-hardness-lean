/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FullSynthesisColumns

/-!
# Full Synthesis Pivot

Eliminate one symplectically paired set of columns.
-/

public section

namespace CliffordSynthesis.Circuit

open Planes (F)
open LocalChart (bit)
open FreeLayers (act pair layer layer_run layer_cost applyFrames)

variable {n : Nat}

private def xFrame : Bool × Bool → Fin 6
  | (true, true) => 2
  | (true, false) => 0
  | (false, _) => 1

private def zFrame : Bool × Bool → Fin 6
  | (true, true) => 5
  | (true, false) => 1
  | (false, _) => 0

private theorem act_xFrame : ∀ p : Bool × Bool, act (xFrame p) p = (p.1 || p.2, false) := by decide

private theorem act_zFrame : ∀ p : Bool × Bool, act (zFrame p) p = (false, p.1 || p.2) := by decide

private theorem act_pair_zero : ∀ f, act f (false, false) = (false, false) := by decide

private theorem act_keep_x :
    ∀ b : Bool, act (if b then 5 else 0) (true, false) = (true, false) := by decide

private theorem act_clear_x :
    ∀ b : Bool, act (if b then 5 else 0) (b, true) = (false, true) := by decide

private theorem prepareX (a : Tableau (n + 1)) (ha : ColumnsSymplectic a) :
    ∃ gs : List (Gate (n + 1)), cost gs ≤ 1 ∧ (run gs a).x 0 (0, false) = true ∧
      ∀ i, (run gs a).z i (0, false) = false := by
  let f := fun i => xFrame (pair a i (0, false))
  let gs := layer f
  let b := run gs a
  have hz (i : Fin (n + 1)) : b.z i (0, false) = false := by
    change (run (layer f) a).z i (0, false) = false
    rw [layer_run]
    exact congrArg Prod.snd (act_xFrame (pair a i (0, false)))
  by_cases h0 : b.x 0 (0, false) = true
  · exact ⟨gs, by simp [gs, layer_cost], h0, hz⟩
  · have hExists : ∃ i, b.x i (0, false) = true := by
      by_contra! h
      have hp := ha.run gs (0, false) (0, true)
      have hsum : columnPairing b (0, false) (0, true) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [wirePairing, pair, bit, h i, hz i]
      have hunit : columnPairing b (0, false) (0, true) = 1 := by simpa using hp
      exact zero_ne_one (hsum.symm.trans hunit)
    obtain ⟨i, hi⟩ := hExists
    have hi0 : i ≠ 0 := fun h => h0 (by simpa [h] using hi)
    refine ⟨gs ++ [.CX i 0 hi0], ?_, ?_, ?_⟩
    · simp [cost_append, gs, layer_cost, cost, paid]
    · rw [run_append]
      change (cnot i 0 b).x 0 (0, false) = true
      simp [cnot, h0, hi]
    · intro j
      rw [run_append]
      change (cnot i 0 b).z j (0, false) = false
      simp [cnot, hz]

private theorem fanX (p : Fin n × Bool) (c : Fin n) (qs : List (Fin n))
    (hc : c ∉ qs) (a : Tableau n) (hp : a.x c p = true) (hz : ∀ i, a.z i p = false) :
    ∃ gs : List (Gate n), cost gs ≤ qs.length ∧
      ∀ i, pair (run gs a) i p = (if i ∈ qs then false else a.x i p, false) := by
  induction qs generalizing a with
  | nil => exact ⟨[], by simp [cost], fun i => by simp [run, pair, hz]⟩
  | cons j qs ih =>
      have hcj : c ≠ j := fun h => hc (List.mem_cons.mpr (Or.inl h))
      have hcq : c ∉ qs := fun h => hc (List.mem_cons.mpr (Or.inr h))
      let step : List (Gate n) := if a.x j p then [.CX c j hcj] else []
      let b := run step a
      have hstep (i : Fin n) : pair b i p = (if i = j then false else a.x i p, false) := by
        by_cases h : a.x j p = true
        · by_cases hji : i = j
          · subst i
            simp [b, step, h, run, applyGate, pair, cnot, hp, hz]
          · simp [b, step, h, run, applyGate, pair, cnot, hji, hz]
        · by_cases hji : i = j
          · subst i
            simp [b, step, h, run, pair, hz]
          · simp [b, step, h, run, pair, hz, hji]
      have hb : b.x c p = true := by
        simpa [pair, hcj, hp] using congrArg Prod.fst (hstep c)
      have hbz (i : Fin n) : b.z i p = false := congrArg Prod.snd (hstep i)
      obtain ⟨gs, hgs, hrs⟩ := ih hcq b hb hbz
      have hcost : cost step ≤ 1 := by
        by_cases h : a.x j p = true <;> simp [step, h, cost, paid]
      refine ⟨step ++ gs, by rw [cost_append]; simp only [List.length_cons]; omega, ?_⟩
      intro i
      rw [run_append, hrs]
      have he := congrArg Prod.fst (hstep i)
      change b.x i p = _ at he
      by_cases hi : i = j
      · subst i
        simp only [ite_eq_left] at he
        simp [he]
      · simp [hi, he]

private def pivotX (a : Tableau n) (c : Fin n) (p : Fin n × Bool) : Prop :=
  ∀ i, pair a i p = (decide (i = c), false)

private def pivotZ (a : Tableau n) (c : Fin n) (p : Fin n × Bool) : Prop :=
  ∀ i, pair a i p = (false, decide (i = c))

private theorem cnot_preserves_pivotX {a : Tableau n} {c j : Fin n} {p : Fin n × Bool}
    (hcj : c ≠ j) (hx : pivotX a c p) : pivotX (cnot j c a) c p := by
  intro i
  have hxi (k : Fin n) : a.x k p = decide (k = c) := congrArg Prod.fst (hx k)
  have hzi (k : Fin n) : a.z k p = false := congrArg Prod.snd (hx k)
  simp [pair, cnot, hxi, hzi, Ne.symm hcj]

private theorem fanZ (p q : Fin n × Bool) (c : Fin n) (qs : List (Fin n))
    (hc : c ∉ qs) (a : Tableau n) (hq : a.z c q = true) (hz : ∀ i, a.x i q = false)
    (hx : pivotX a c p) :
    ∃ gs : List (Gate n), cost gs ≤ qs.length ∧ pivotX (run gs a) c p ∧
      ∀ i, pair (run gs a) i q = (false, if i ∈ qs then false else a.z i q) := by
  induction qs generalizing a with
  | nil =>
      exact ⟨[], by simp [cost], hx, fun i => by simp [run, pair, hz]⟩
  | cons j qs ih =>
      have hcj : c ≠ j := fun h => hc (List.mem_cons.mpr (Or.inl h))
      have hcq : c ∉ qs := fun h => hc (List.mem_cons.mpr (Or.inr h))
      let step : List (Gate n) := if a.z j q then [.CX j c (Ne.symm hcj)] else []
      let b := run step a
      have hstep (i : Fin n) : pair b i q = (false, if i = j then false else a.z i q) := by
        by_cases h : a.z j q = true
        · by_cases hji : i = j
          · subst i
            simp [b, step, h, run, applyGate, pair, cnot, hq, hz]
          · simp [b, step, h, run, applyGate, pair, cnot, hji, hz]
        · by_cases hji : i = j
          · subst i
            simp [b, step, h, run, pair, hz]
          · simp [b, step, h, run, pair, hz, hji]
      have hpivot : pivotX b c p := by
        by_cases h : a.z j q = true
        · simpa [b, step, h, run, applyGate] using cnot_preserves_pivotX hcj hx
        · simpa [b, step, h, run] using hx
      have hb : b.z c q = true := by
        simpa [pair, hcj, hq] using congrArg Prod.snd (hstep c)
      have hbx (i : Fin n) : b.x i q = false := congrArg Prod.fst (hstep i)
      obtain ⟨gs, hgs, hpx, hzs⟩ := ih hcq b hb hbx hpivot
      have hcost : cost step ≤ 1 := by
        by_cases h : a.z j q = true <;> simp [step, h, cost, paid]
      refine ⟨step ++ gs, by rw [cost_append]; simp only [List.length_cons]; omega,
        by simpa [run_append] using hpx, ?_⟩
      intro i
      rw [run_append, hzs]
      have he := congrArg Prod.snd (hstep i)
      change b.z i q = _ at he
      by_cases hi : i = j
      · subst i
        simp only [ite_eq_left] at he
        simp [he]
      · simp [hi, he]

private theorem pairing_pivotX {a : Tableau (n + 1)} {p : Fin (n + 1) × Bool}
    (hx : pivotX a 0 p) (q : Fin (n + 1) × Bool) : columnPairing a p q = bit (a.z 0 q) := by
  have h (i : Fin (n + 1)) : pair a i p = (decide (i = 0), false) := hx i
  simp only [columnPairing, Fin.sum_univ_succ, h]
  simp [wirePairing, pair, show bit false = 0 from rfl, show bit true = 1 from rfl]

private theorem pairing_pivotZ {a : Tableau (n + 1)} {p : Fin (n + 1) × Bool}
    (hz : pivotZ a 0 p) (q : Fin (n + 1) × Bool) : columnPairing a p q = bit (a.x 0 q) := by
  have h (i : Fin (n + 1)) : pair a i p = (false, decide (i = 0)) := hz i
  simp only [columnPairing, Fin.sum_univ_succ, h]
  simp [wirePairing, pair, show bit false = 0 from rfl, show bit true = 1 from rfl]

private theorem prepareZ (a : Tableau (n + 1)) (ha : ColumnsSymplectic a)
    (hx : pivotX a 0 (0, false)) :
    ∃ gs : List (Gate (n + 1)), cost gs = 0 ∧ pivotX (run gs a) 0 (0, false) ∧
      (run gs a).z 0 (0, true) = true ∧ ∀ i, (run gs a).x i (0, true) = false := by
  have hz : a.z 0 (0, true) = true := by
    have he := ha (0, false) (0, true)
    rw [pairing_pivotX hx] at he
    simpa [bit] using he
  let f : Fin (n + 1) → Fin 6 := fun i =>
    if i = 0 then (if a.x 0 (0, true) then 5 else 0) else zFrame (pair a i (0, true))
  have hout (i : Fin (n + 1)) :
      pair (run (layer f) a) i (0, true) =
        (false, if i = 0 then true else a.x i (0, true) || a.z i (0, true)) := by
    rw [layer_run]
    change act (f i) (pair a i (0, true)) = _
    by_cases hi : i = 0
    · subst i
      simpa [f, pair, hz] using act_clear_x (a.x 0 (0, true))
    · simpa [f, hi, pair] using act_zFrame (pair a i (0, true))
  refine ⟨layer f, layer_cost f, ?_, ?_, fun i => congrArg Prod.fst (hout i)⟩
  · intro i
    rw [layer_run]
    change act (f i) (pair a i (0, false)) = _
    rw [hx i]
    by_cases hi : i = 0
    · subst i
      simpa [f] using act_keep_x (a.x 0 (0, true))
    · simpa [hi] using act_pair_zero (f i)
  · simpa [pair] using congrArg Prod.snd (hout 0)

private def tailIndices (n : Nat) : List (Fin (n + 1)) := (List.finRange n).map Fin.succ

private theorem mem_tailIndices (i : Fin (n + 1)) : i ∈ tailIndices n ↔ i ≠ 0 := by
  simp only [tailIndices, List.mem_map, List.mem_finRange, true_and]
  refine ⟨fun ⟨j, hj⟩ => hj ▸ Fin.succ_ne_zero j, fun h => ?_⟩
  exact ⟨i.pred h, Fin.succ_pred i h⟩

/-- Clear the columns corresponding to the first qubit using at most 2n+1 CNOTs. -/
theorem clear_first_qubit (a : Tableau (n + 1)) (ha : ColumnsSymplectic a) :
    ∃ gs : List (Gate (n + 1)), cost gs ≤ 2 * n + 1 ∧
      (∀ i, pair (run gs a) i (0, false) = (decide (i = 0), false)) ∧
      (∀ i, pair (run gs a) i (0, true) = (false, decide (i = 0))) := by
  have hmem : (0 : Fin (n + 1)) ∉ tailIndices n := fun h => (mem_tailIndices 0).mp h rfl
  have hlen : (tailIndices n).length = n := by simp [tailIndices]
  obtain ⟨g₁, hn₁, h₁, hz₁⟩ := prepareX a ha
  obtain ⟨g₂, hn₂, h₂⟩ := fanX (0, false) 0 (tailIndices n) hmem (run g₁ a) h₁ hz₁
  have hx : pivotX (run g₂ (run g₁ a)) 0 (0, false) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa [hmem, h₁] using h₂ 0
    · simpa [(mem_tailIndices i).mpr hi, hi] using h₂ i
  obtain ⟨g₃, hn₃, hx₃, h₃, hz₃⟩ := prepareZ _ ((ha.run g₁).run g₂) hx
  obtain ⟨g₄, hn₄, hx₄, h₄⟩ := fanZ (0, false) (0, true) 0 (tailIndices n) hmem _ h₃ hz₃ hx₃
  refine ⟨g₁ ++ g₂ ++ g₃ ++ g₄, ?_, ?_, ?_⟩
  · simp only [cost_append]
    omega
  · simpa only [run_append, pivotX] using hx₄
  · simp only [run_append]
    intro i
    by_cases hi : i = 0
    · subst i
      simpa [hmem, h₃] using h₄ 0
    · simpa [(mem_tailIndices i).mpr hi, hi] using h₄ i

/-- Symplecticity forces the first wire's remaining entries to vanish once its two columns are fixed. -/
theorem cleared_head_zero {a : Tableau (n + 1)} (ha : ColumnsSymplectic a)
    (hx : ∀ i, pair a i (0, false) = (decide (i = 0), false))
    (hz : ∀ i, pair a i (0, true) = (false, decide (i = 0))) (i : Fin n) (b : Bool) :
    pair a 0 (i.succ, b) = (false, false) := by
  have h₁ := ha (0, true) (i.succ, b)
  have h₂ := ha (0, false) (i.succ, b)
  rw [pairing_pivotZ hz] at h₁
  rw [pairing_pivotX hx] at h₂
  have h₁' : a.x 0 (i.succ, b) = false := by simpa [bit, Ne.symm (Fin.succ_ne_zero i)] using h₁
  have h₂' : a.z 0 (i.succ, b) = false := by simpa [bit, Ne.symm (Fin.succ_ne_zero i)] using h₂
  exact Prod.ext h₁' h₂'

end CliffordSynthesis.Circuit
