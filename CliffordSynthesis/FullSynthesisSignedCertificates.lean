/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FullSynthesisSigned
public import CliffordSynthesis.FullSynthesisSignedLocals
public import CliffordSynthesis.FullSwapWords

/-!
# Full Synthesis Signed Certificates

Move free swaps to the output and cap signed synthesis certificates by the
number of paid gates and the local layers between them.
-/

@[expose] public section

namespace CliffordSynthesis.SignedCircuit

variable {n : Nat}

private def reorder (p : Equiv.Perm (Fin n)) (T : Tableau n) : Tableau n :=
  ⟨FreeSwaps.reorder p T.linear, T.sign⟩

private theorem reorder_one (T : Tableau n) : reorder (Equiv.refl _) T = T := by
  cases T
  rfl

private def relabel (p : Equiv.Perm (Fin n)) : Step n → Step n
  | .single i g => .single (p i) g
  | .two c t hct g => .two (p c) (p t) (fun h => hct (p.injective h)) g
  | .swap i j => .swap (p i) (p j)

private theorem map_swap (p : Equiv.Perm (Fin n)) (i j k : Fin n) :
    p (Equiv.swap i j k) = Equiv.swap (p i) (p j) (p k) := by
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [Equiv.swap_apply_def, hi, hj]

private theorem step_reorder (g : Step n) (p : Equiv.Perm (Fin n)) (T : Tableau n) :
    applyStep g (reorder p T) = reorder p (applyStep (relabel p g) T) := by
  apply tableau_ext
  · apply FreeLayers.tableau_ext
    intro i j
    cases g with
    | single q g =>
        by_cases h : i = q <;>
          simp [applyStep, reorder, relabel, FreeSwaps.reorder, FreeLayers.applyFrames,
            FreeLayers.pair, h]
    | two c t hct g =>
        simp [applyStep, reorder, relabel, FreeSwaps.reorder, FreeLayers.pair, TwoQubit.read,
          TwoQubit.update]
    | swap i j =>
        simp [applyStep, reorder, relabel, FreeSwaps.reorder, FreeLayers.pair, map_swap]
  · intro j
    cases g <;>
      simp [applyStep, reorder, relabel, FreeSwaps.reorder, FreeLayers.pair, TwoQubit.read]

private theorem run_reorder (gs : List (Step n)) (p : Equiv.Perm (Fin n)) (T : Tableau n) :
    run gs (reorder p T) = reorder p (run (gs.map (relabel p)) T) := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih => simp only [run, step_reorder, ih, List.map_cons]

private theorem cost_relabel (gs : List (Step n)) (p : Equiv.Perm (Fin n)) (a b : Nat) :
    cost a b (gs.map (relabel p)) = cost a b gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [cost, relabel, Step.weight, ih]

private theorem allowed_relabel (Γ : Set TwoGate) (p : Equiv.Perm (Fin n)) (g : Step n)
    (h : g.allowed Γ false) : (relabel p g).allowed Γ false := by
  cases g <;> exact h

private theorem remove_swaps (Γ : Set TwoGate) (a b : Nat) (swaps : Bool)
    (gs : List (Step n)) (h : ∀ g ∈ gs, g.allowed Γ swaps) :
    ∃ (p : Equiv.Perm (Fin n)) (cs : List (Step n)),
      (∀ g ∈ cs, g.allowed Γ false) ∧ cost a b cs = cost a b gs ∧
      (swaps = false → p = Equiv.refl _) ∧ ∀ T, run gs T = reorder p (run cs T) := by
  induction gs with
  | nil => exact ⟨Equiv.refl _, [], by simp, rfl, fun _ => rfl, fun T => (reorder_one T).symm⟩
  | cons g gs ih =>
      have hg := h g (by simp)
      obtain ⟨p, cs, ha, hw, hp, hr⟩ := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      cases g with
      | single i g =>
          refine ⟨p, .single i g :: cs, ?_, by simp [cost, hw], hp, fun T => hr _⟩
          exact List.forall_mem_cons.mpr ⟨trivial, ha⟩
      | two c t hct g =>
          refine ⟨p, .two c t hct g :: cs, ?_, by simp [cost, hw], hp, fun T => hr _⟩
          exact List.forall_mem_cons.mpr ⟨hg, ha⟩
      | swap i j =>
          let q := Equiv.swap i j
          refine ⟨p.trans q, cs.map (relabel q), ?_, ?_, ?_, fun T => ?_⟩
          · intro s hs
            obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hs
            exact allowed_relabel Γ q g (ha g hg)
          · simpa [cost, Step.weight, cost_relabel] using hw
          · intro hf
            simp [Step.allowed, hf] at hg
          · change run gs (reorder q T) = _
            rw [hr, run_reorder]
            rfl

private def swapsOf (ss : List (Fin n × Fin n)) : List (Step n) :=
  ss.map fun ij => .swap ij.1 ij.2

private theorem run_swaps (ss : List (Fin n × Fin n)) (T : Tableau n) :
    run (swapsOf ss) T = reorder (ss.map (fun ij => Equiv.swap ij.1 ij.2)).prod T := by
  apply tableau_ext
  · have h (s : List (Fin n × Fin n)) (U : Tableau n) :
        (run (swapsOf s) U).linear =
          FreeSwaps.execute (s.map (fun ij => FreeSwaps.Step.swap ij.1 ij.2)) U.linear := by
      induction s generalizing U with
      | nil => rfl
      | cons ij s ih => exact ih _
    rw [h, FreeSwaps.execute_swap_word]
    rfl
  · intro j
    induction ss generalizing T with
    | nil => rfl
    | cons ij ss ih => exact ih _

private theorem cost_swaps (a b : Nat) (ss : List (Fin n × Fin n)) :
    cost a b (swapsOf ss) = 0 := by
  induction ss with
  | nil => rfl
  | cons ij ss ih =>
      change 0 + cost a b (swapsOf ss) = 0
      simp [ih]

private theorem restore_swaps (Γ : Set TwoGate) (a b : Nat) (swaps : Bool)
    (p : Equiv.Perm (Fin n)) (h : swaps = false → p = Equiv.refl _) :
    ∃ ss : List (Step n), (∀ g ∈ ss, g.allowed Γ swaps) ∧ cost a b ss = 0 ∧
      ss.length ≤ n ∧ ∀ T, run ss T = reorder p T := by
  cases swaps with
  | false =>
      rw [h rfl]
      exact ⟨[], by simp, rfl, Nat.zero_le _, fun T => (reorder_one T).symm⟩
  | true =>
      obtain ⟨ss, hl, hp⟩ := FreeSwaps.short_swap_word p
      refine ⟨swapsOf ss, ?_, cost_swaps a b ss, by simpa [swapsOf] using hl, fun T => ?_⟩
      · intro g hg
        obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hg
        rfl
      · rw [run_swaps, hp]

private theorem length_le_cost (Γ : Set TwoGate) (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (gs : List (Step n)) (h : ∀ g ∈ gs, g.allowed Γ false) : gs.length ≤ cost a b gs := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
      have hg := h g (by simp)
      have hw : 1 ≤ g.weight a b := by
        cases g with
        | single => exact ha
        | two => exact hb
        | swap => simp [Step.allowed] at hg
      have hl := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      simp only [List.length_cons, cost]
      omega

private theorem normalize_paid (Γ : Set TwoGate) (a b : Nat) (hb : 0 < b)
    (gs : List (Step n)) (h : ∀ g ∈ gs, g.allowed Γ false) :
    ∃ cs : List (Step n), (∀ g ∈ cs, g.allowed Γ false) ∧ cost a b cs = cost a b gs ∧
      cs.length ≤ n + (n + 1) * cost a b gs ∧ ∀ T, run cs T = run gs T := by
  cases a with
  | zero => exact compress_free_locals Γ b hb gs h
  | succ a =>
      refine ⟨gs, h, rfl, ?_, fun _ => rfl⟩
      have hcost := length_le_cost Γ (a + 1) b (Nat.succ_pos _) hb gs h
      have hmul : cost (a + 1) b gs ≤ (n + 1) * cost (a + 1) b gs :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      exact hcost.trans (hmul.trans (Nat.le_add_left _ _))

private theorem run_append (gs hs : List (Step n)) (T : Tableau n) :
    run (gs ++ hs) T = run hs (run gs T) := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem cost_append (a b : Nat) (gs hs : List (Step n)) :
    cost a b (gs ++ hs) = cost a b gs + cost a b hs := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih => simp [cost, ih, Nat.add_assoc]

/-- A signed witness needs only one local step per wire between paid gates
and at most one final swap per wire. -/
def certificateLength (a b n : Nat) : Nat :=
  (n + 1) * (fullSynthesisCap a b n + 1) + n

theorem certificateLength_le (a b n : Nat) :
    certificateLength a b n ≤ (4 * (a + b) + 2) * (n + 1) ^ 4 := by
  have hlen : n + 3 * n * (n ^ 2 + 1) + n ^ 2 ≤ 4 * (n + 1) ^ 3 := by nlinarith
  have hcap := Nat.mul_le_mul_left (a + b) hlen
  have hpow : n + 1 ≤ (n + 1) ^ 4 := by
    nlinarith
  calc
    _ = (n + 1) * fullSynthesisCap a b n + (n + 1 + n) := by rw [certificateLength, Nat.mul_add]; omega
    _ ≤ (n + 1) * ((a + b) * (4 * (n + 1) ^ 3)) + 2 * (n + 1) ^ 4 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hcap) (by omega)
    _ = _ := by ring

theorem bounded_certificate (Γ : Set TwoGate) (a b : Nat) (hb : 0 < b) (swaps : Bool)
    (hΓ : cnotGate ∈ Γ) (target : Tableau n) (k : Nat)
    (h : Synthesizes Γ a b swaps target k) :
    ∃ gs : List (Step n), (∀ g ∈ gs, g.allowed Γ swaps) ∧ cost a b gs ≤ k ∧
      gs.length ≤ certificateLength a b n ∧ Same (run gs (identity n)) target := by
  have hc : Synthesizes Γ a b swaps target (min k (fullSynthesisCap a b n)) := by
    rcases le_total k (fullSynthesisCap a b n) with hk | hk
    · rwa [min_eq_left hk]
    · rw [min_eq_right hk]
      exact full_synthesis_bound Γ a b swaps hΓ target k h
  obtain ⟨gs, ha, hw, hs⟩ := hc
  obtain ⟨p, cs, hca, hcw, hp, hrun⟩ := remove_swaps Γ a b swaps gs ha
  obtain ⟨ds, hda, hdw, hdl, hdr⟩ := normalize_paid Γ a b hb cs hca
  obtain ⟨ss, hsa, hsw, hsl, hsr⟩ := restore_swaps Γ a b swaps p hp
  refine ⟨ds ++ ss, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · have hd := hda g hg
      cases g with
      | single => trivial
      | two => exact hd
      | swap => simp [Step.allowed] at hd
    · exact hsa g hg
  · rw [cost_append, hsw, Nat.add_zero, hdw, hcw]
    exact hw.trans (min_le_left _ _)
  · have hcap := hw.trans (min_le_right _ _)
    rw [hcw] at hdl
    have hmul := Nat.mul_le_mul_left (n + 1) hcap
    simp only [certificateLength, List.length_append, Nat.mul_add, Nat.mul_one]
    omega
  · rwa [run_append, hsr, hdr, ← hrun]

end CliffordSynthesis.SignedCircuit
