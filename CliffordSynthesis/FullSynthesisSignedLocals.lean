/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.SignedCircuit
public import CliffordSynthesis.LocalChart

/-!
# Full Synthesis Signed Locals

Compress free signed single-qubit steps into one layer between paid gates.
-/

public section

namespace CliffordSynthesis.SignedCircuit

open FreeLayers (act pair)
open LocalChart (bit bit_xor)

variable {n : Nat}

theorem tableau_ext {T U : Tableau n} (h : T.linear = U.linear)
    (hs : ∀ p, T.sign p = U.sign p) : T = U := by
  have he := funext hs
  cases T
  cases U
  cases h
  cases he
  rfl

private def localSign (g : LocalGate) (v : Bool × Bool) : Bool :=
  signChange (TwoQubit.localAction g.1 0) (g.2.1, g.2.2, false, false)
    (v.1, v.2, false, false)

private def identityLocal : LocalGate := (0, false, false)

private theorem identityLocal_sign : ∀ v, localSign identityLocal v = false := by decide

private def composedFrame (g h : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? fun k => decide (∀ v : Bool × Bool, act k v = act h (act g v))).getD 0

private def composeLocal (g h : LocalGate) : LocalGate :=
  let sign v := localSign g v ^^ localSign h (act g.1 v)
  (composedFrame g.1 h.1, sign (true, false), sign (false, true))

private theorem composeLocal_linear :
    ∀ (g h : LocalGate) (v : Bool × Bool),
      act (composeLocal g h).1 v = act h.1 (act g.1 v) := by decide

private theorem composeLocal_sign :
    ∀ (g h : LocalGate) (v : Bool × Bool),
      localSign (composeLocal g h) v = (localSign g v ^^ localSign h (act g.1 v)) := by
  decide

private theorem single_pair (q : Fin n) (g : LocalGate) (T : Tableau n)
    (i : Fin n) (p : Fin n × Bool) :
    pair (applyStep (.single q g) T).linear i p =
      if i = q then act g.1 (pair T.linear i p) else pair T.linear i p := by
  by_cases h : i = q <;> simp [applyStep, FreeLayers.applyFrames, pair, h, FreeLayers.act_zero]

private theorem single_sign (q : Fin n) (g : LocalGate) (T : Tableau n) (p : Fin n × Bool) :
    (applyStep (.single q g) T).sign p = (T.sign p ^^ localSign g (pair T.linear q p)) := rfl

private def layerOn (f : Fin n → LocalGate) (qs : List (Fin n)) : List (Step n) :=
  qs.map fun i => .single i (f i)

private theorem layerOn_pair (f : Fin n → LocalGate) (qs : List (Fin n)) (hn : qs.Nodup)
    (T : Tableau n) (i : Fin n) (p : Fin n × Bool) :
    pair (run (layerOn f qs) T).linear i p =
      if i ∈ qs then act (f i).1 (pair T.linear i p) else pair T.linear i p := by
  induction qs generalizing T with
  | nil => simp [layerOn, run]
  | cons j qs ih =>
      rw [List.nodup_cons] at hn
      change pair (run (layerOn f qs) (applyStep (.single j (f j)) T)).linear i p = _
      rw [ih hn.2, single_pair]
      by_cases h : i = j
      · subst i
        simp [hn.1]
      · simp [h]

private theorem layerOn_sign (f : Fin n → LocalGate) (qs : List (Fin n)) (hn : qs.Nodup)
    (T : Tableau n) (p : Fin n × Bool) :
    bit ((run (layerOn f qs) T).sign p) =
      bit (T.sign p) + ∑ i ∈ qs.toFinset, bit (localSign (f i) (pair T.linear i p)) := by
  induction qs generalizing T with
  | nil => simp [layerOn, run]
  | cons j qs ih =>
      rw [List.nodup_cons] at hn
      change bit ((run (layerOn f qs) (applyStep (.single j (f j)) T)).sign p) = _
      have hj : j ∉ qs.toFinset := by simpa using hn.1
      rw [ih hn.2, single_sign, bit_xor, List.toFinset_cons, Finset.sum_insert hj, add_assoc]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have he : i ≠ j := fun h => hn.1 (h ▸ List.mem_toFinset.mp hi)
      rw [single_pair, ite_eq_right he]

private def layer (f : Fin n → LocalGate) : List (Step n) := layerOn f (List.finRange n)

private theorem layer_length (f : Fin n → LocalGate) : (layer f).length = n := by
  simp [layer, layerOn]

private theorem layer_allowed (Γ : Set TwoGate) (f : Fin n → LocalGate) (g : Step n)
    (h : g ∈ layer f) : g.allowed Γ false := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  trivial

private theorem layer_cost (b : Nat) (f : Fin n → LocalGate) : cost 0 b (layer f) = 0 := by
  have h (qs : List (Fin n)) : cost 0 b (layerOn f qs) = 0 := by
    induction qs with
    | nil => rfl
    | cons j qs ih =>
        change 0 + cost 0 b (layerOn f qs) = 0
        simp [ih]
  exact h _

private theorem layer_pair (f : Fin n → LocalGate) (T : Tableau n) (i : Fin n)
    (p : Fin n × Bool) :
    pair (run (layer f) T).linear i p = act (f i).1 (pair T.linear i p) := by
  simp [layer, layerOn_pair f _ (List.nodup_finRange n)]

private theorem layer_sign (f : Fin n → LocalGate) (T : Tableau n) (p : Fin n × Bool) :
    bit ((run (layer f) T).sign p) =
      bit (T.sign p) + ∑ i, bit (localSign (f i) (pair T.linear i p)) := by
  unfold layer
  rw [layerOn_sign _ _ (List.nodup_finRange n)]
  have h : (List.finRange n).toFinset = Finset.univ := by ext i; simp
  rw [h]

private theorem bit_inj : Function.Injective bit := by unfold Function.Injective; decide

private theorem layer_identity (T : Tableau n) : run (layer (fun _ => identityLocal)) T = T := by
  apply tableau_ext
  · apply FreeLayers.tableau_ext
    intro i p
    rw [layer_pair]
    exact FreeLayers.act_zero _
  · intro p
    apply bit_inj
    simp [layer_sign, identityLocal_sign, show bit false = 0 from rfl]

private theorem layer_prepend (f : Fin n → LocalGate) (q : Fin n) (g : LocalGate) (T : Tableau n) :
    run (layer (Function.update f q (composeLocal g (f q)))) T =
      run (layer f) (applyStep (.single q g) T) := by
  let T' := applyStep (.single q g) T
  let f' := Function.update f q (composeLocal g (f q))
  change run (layer f') T = run (layer f) T'
  apply tableau_ext
  · apply FreeLayers.tableau_ext
    intro i p
    rw [layer_pair, layer_pair, single_pair]
    by_cases hi : i = q
    · subst i
      simpa [f'] using composeLocal_linear g (f q) (pair T.linear q p)
    · simp [f', hi]
  · intro p
    apply bit_inj
    rw [layer_sign, layer_sign, single_sign, bit_xor]
    let u := fun i => bit (localSign (f' i) (pair T.linear i p))
    let v := fun i => bit (localSign (f i) (pair T'.linear i p))
    change bit (T.sign p) + ∑ i, u i =
      bit (T.sign p) + bit (localSign g (pair T.linear q p)) + ∑ i, v i
    have hq : q ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ u hq, ← Finset.sum_erase_add _ v hq]
    have hsum : ∑ i ∈ Finset.univ.erase q, u i = ∑ i ∈ Finset.univ.erase q, v i := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := (Finset.mem_erase.mp hi).1
      simp [u, v, f', T', single_pair, he]
    have hu : u q = bit (localSign g (pair T.linear q p)) + v q := by
      simp [u, v, f', T', single_pair, composeLocal_sign, bit_xor]
    rw [hsum, hu]
    ring

private theorem run_app (gs hs : List (Step n)) (T : Tableau n) :
    run (gs ++ hs) T = run hs (run gs T) := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem cost_app (a b : Nat) (gs hs : List (Step n)) :
    cost a b (gs ++ hs) = cost a b gs + cost a b hs := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih => simp [cost, ih, Nat.add_assoc]

private theorem normalize_head (Γ : Set TwoGate) (b : Nat) (hb : 0 < b)
    (gs : List (Step n)) (h : ∀ g ∈ gs, g.allowed Γ false) :
    ∃ f : Fin n → LocalGate, ∃ cs : List (Step n),
      (∀ g ∈ cs, g.allowed Γ false) ∧ cost 0 b cs = cost 0 b gs ∧
      cs.length ≤ (n + 1) * cost 0 b gs ∧
      ∀ T, run gs T = run cs (run (layer f) T) := by
  induction gs with
  | nil => exact ⟨fun _ => identityLocal, [], by simp, rfl, by simp [cost],
      fun T => by simp [run, layer_identity]⟩
  | cons g gs ih =>
      obtain ⟨f, cs, ha, hw, hl, hr⟩ := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      cases g with
      | single i g =>
          refine ⟨Function.update f i (composeLocal g (f i)), cs, ha, ?_, ?_, fun T => ?_⟩
          · simpa [cost, Step.weight] using hw
          · simpa [cost, Step.weight] using hl
          · change run gs (applyStep (.single i g) T) = _
            rw [hr, layer_prepend]
      | two c t hct g =>
          refine ⟨fun _ => identityLocal, .two c t hct g :: (layer f ++ cs), ?_, ?_, ?_, fun T => ?_⟩
          · intro s hs
            rcases List.mem_cons.mp hs with hs | hs
            · subst s
              exact h _ (by simp)
            · exact (List.mem_append.mp hs).elim (layer_allowed Γ f s) (ha s)
          · simp [cost, Step.weight, hw, cost_app, layer_cost]
          · simp only [List.length_cons, List.length_append, layer_length, cost, Step.weight,
              Nat.mul_add]
            have hnb : n + 1 ≤ (n + 1) * b := Nat.le_mul_of_pos_right _ hb
            omega
          · change run gs (applyStep (.two c t hct g) T) =
              run (layer f ++ cs) (applyStep (.two c t hct g) (run (layer (fun _ => identityLocal)) T))
            rw [layer_identity, run_app, hr]
      | swap i j =>
          have hf : false = true := h (.swap i j) (by simp)
          contradiction

/-- A free local layer needs at most one signed single-qubit gate per wire. -/
theorem compress_free_locals (Γ : Set TwoGate) (b : Nat) (hb : 0 < b)
    (gs : List (Step n)) (h : ∀ g ∈ gs, g.allowed Γ false) :
    ∃ cs : List (Step n), (∀ g ∈ cs, g.allowed Γ false) ∧ cost 0 b cs = cost 0 b gs ∧
      cs.length ≤ n + (n + 1) * cost 0 b gs ∧ ∀ T, run cs T = run gs T := by
  obtain ⟨f, cs, ha, hw, hl, hr⟩ := normalize_head Γ b hb gs h
  refine ⟨layer f ++ cs, ?_, by simp [cost_app, layer_cost, hw], ?_, fun T => ?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (layer_allowed Γ f g) (ha g)
  · simpa only [List.length_append, layer_length] using Nat.add_le_add_left hl n
  · rw [run_app, hr]

end CliffordSynthesis.SignedCircuit
