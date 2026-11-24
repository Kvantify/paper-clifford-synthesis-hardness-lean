/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.FullVerifier
public import CliffordSynthesis.FullSwapWords
public import CliffordSynthesis.FullSynthesisBound
public import CliffordSynthesis.FullSynthesisPermutations

/-!
# Full Certificates

Polynomial-length phase-free circuits with arbitrary binary thresholds.
-/

public section

namespace CliffordFrontier.FullVerifier

open CliffordSynthesis
open CliffordSynthesis.TwoQubit (Step StepWithSwap)

variable {n : Nat}

private def relabel (p : Equiv.Perm (Fin n)) : Step n → Step n
  | .H i => .H (p i)
  | .S i => .S (p i)
  | .two c t h m => .two (p c) (p t) (fun he => h (p.injective he)) m

private theorem apply_reorder (g : Step n) (p : Equiv.Perm (Fin n)) (a : Circuit.Tableau n) :
    TwoQubit.applyStep g (FreeSwaps.reorder p a) =
      FreeSwaps.reorder p (TwoQubit.applyStep (relabel p g) a) := by
  apply FreeLayers.tableau_ext
  intro i j
  cases g <;>
    simp [FreeLayers.pair, FreeSwaps.reorder, TwoQubit.applyStep, TwoQubit.update,
      TwoQubit.read, relabel, Circuit.hadamard, Circuit.phase]

private theorem run_reorder (cs : List (Step n)) (p : Equiv.Perm (Fin n))
    (a : Circuit.Tableau n) :
    TwoQubit.run cs (FreeSwaps.reorder p a) =
      FreeSwaps.reorder p (TwoQubit.run (cs.map (relabel p)) a) := by
  induction cs generalizing a with
  | nil => rfl
  | cons g cs ih => simp only [TwoQubit.run, apply_reorder, ih, List.map_cons]

private theorem relabel_cost (cs : List (Step n)) (p : Equiv.Perm (Fin n)) :
    TwoQubit.cost (cs.map (relabel p)) = TwoQubit.cost cs := by
  induction cs with
  | nil => rfl
  | cons g cs ih => cases g <;> simp [TwoQubit.cost, TwoQubit.paid, relabel, ih]

private theorem relabel_allowed (Γ : Set TwoQubit.Gate) (p : Equiv.Perm (Fin n)) (g : Step n)
    (h : TwoQubit.Allowed Γ g) : TwoQubit.Allowed Γ (relabel p g) := by
  cases g <;> exact h

private theorem separate_swaps (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (gs : List (StepWithSwap n)) (h : ∀ g ∈ gs, Allowed Γ swaps g) :
    ∃ p : Equiv.Perm (Fin n), ∃ cs : List (Step n),
      TwoQubit.cost cs = StepWithSwap.cost gs ∧ (∀ g ∈ cs, TwoQubit.Allowed Γ g) ∧
      (swaps = true ∨ p = Equiv.refl _) ∧
      ∀ a, StepWithSwap.run gs a = FreeSwaps.reorder p (TwoQubit.run cs a) := by
  induction gs with
  | nil => exact ⟨Equiv.refl _, [], rfl, by simp, Or.inr rfl, fun a => (FreeSwaps.reorder_one a).symm⟩
  | cons g gs ih =>
    have hg := h g (List.mem_cons_self)
    obtain ⟨p, cs, hc, ha, hp, hr⟩ := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    cases g with
    | gate g =>
      refine ⟨p, g :: cs, congrArg (TwoQubit.paid g + ·) hc, ?_, hp, fun a => hr _⟩
      exact List.forall_mem_cons.mpr ⟨hg, ha⟩
    | swap i j =>
      let s := Equiv.swap i j
      refine ⟨p.trans s, cs.map (relabel s), (relabel_cost cs s).trans hc, ?_, Or.inl hg, ?_⟩
      · intro g hg
        obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
        exact relabel_allowed Γ s g (ha g hmem)
      · intro a
        change StepWithSwap.run gs (FreeSwaps.reorder s a) =
          FreeSwaps.reorder (p.trans s) (TwoQubit.run (cs.map (relabel s)) a)
        rw [hr, run_reorder, FreeSwaps.reorder_reorder]

private abbrev localLayer (f : Fin n → Fin 6) : List (Step n) :=
  (FreeLayers.layer f).map TwoQubit.ofGate

private theorem local_cost (f : Fin n → Fin 6) : TwoQubit.cost (localLayer f) = 0 :=
  (TwoQubit.ofGate_cost _).trans (FreeLayers.layer_cost f)

private theorem local_run (f : Fin n → Fin 6) (a : Circuit.Tableau n) :
    TwoQubit.run (localLayer f) a = FreeLayers.applyFrames f a :=
  (TwoQubit.ofGate_run _ _).trans (FreeLayers.layer_run f a)

private theorem local_allowed (Γ : Set TwoQubit.Gate) (f : Fin n → Fin 6) :
    ∀ g ∈ localLayer f, TwoQubit.Allowed Γ g :=
  TwoQubit.zero_cost_allowed Γ _ (local_cost f)

private theorem normalize_head (Γ : Set TwoQubit.Gate) (gs : List (Step n))
    (h : ∀ g ∈ gs, TwoQubit.Allowed Γ g) :
    ∃ f : Fin n → Fin 6, ∃ cs : List (Step n),
      TwoQubit.cost cs = TwoQubit.cost gs ∧ (∀ g ∈ cs, TwoQubit.Allowed Γ g) ∧
      cs.length ≤ (3 * n + 1) * TwoQubit.cost gs ∧
      ∀ a, TwoQubit.run gs a = TwoQubit.run cs (FreeLayers.applyFrames f a) := by
  induction gs with
  | nil => exact ⟨fun _ => 0, [], rfl, by simp, by simp, fun _ => rfl⟩
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    obtain ⟨f, cs, hc, ha, hl, hr⟩ := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    cases g with
    | H i =>
      refine ⟨Function.update f i (FreeLayers.preH (f i)), cs, ?_, ha, ?_, ?_⟩
      · simpa only [TwoQubit.cost, TwoQubit.paid, Nat.zero_add] using hc
      · simpa only [TwoQubit.cost, TwoQubit.paid, Nat.zero_add] using hl
      · intro a
        change TwoQubit.run gs (Circuit.hadamard i a) = _
        rw [hr, FreeLayers.frames_preH]
    | S i =>
      refine ⟨Function.update f i (FreeLayers.preS (f i)), cs, ?_, ha, ?_, ?_⟩
      · simpa only [TwoQubit.cost, TwoQubit.paid, Nat.zero_add] using hc
      · simpa only [TwoQubit.cost, TwoQubit.paid, Nat.zero_add] using hl
      · intro a
        change TwoQubit.run gs (Circuit.phase i a) = _
        rw [hr, FreeLayers.frames_preS]
    | two c t hct m =>
      refine ⟨fun _ => 0, .two c t hct m :: (localLayer f ++ cs), ?_, ?_, ?_, ?_⟩
      · change 1 + TwoQubit.cost (localLayer f ++ cs) = 1 + TwoQubit.cost gs
        rw [TwoQubit.cost_append, local_cost, Nat.zero_add, hc]
      · exact List.forall_mem_cons.mpr
          ⟨hg, List.forall_mem_append.mpr ⟨local_allowed Γ f, ha⟩⟩
      · have hf := FreeLayers.layer_length f
        change (.two c t hct m :: (localLayer f ++ cs)).length ≤
          (3 * n + 1) * (1 + TwoQubit.cost gs)
        simp only [List.length_cons, List.length_append, localLayer, List.length_map,
          Nat.mul_add, Nat.mul_one]
        omega
      · intro a
        change TwoQubit.run gs (TwoQubit.applyStep (.two c t hct m) a) =
          TwoQubit.run (localLayer f ++ cs)
            (TwoQubit.applyStep (.two c t hct m) (FreeLayers.applyFrames (fun _ => 0) a))
        rw [FreeLayers.frames_zero, TwoQubit.run_append, local_run, hr]

private theorem normalize_local (Γ : Set TwoQubit.Gate) (gs : List (Step n))
    (h : ∀ g ∈ gs, TwoQubit.Allowed Γ g) :
    ∃ cs : List (Step n), TwoQubit.cost cs = TwoQubit.cost gs ∧
      (∀ g ∈ cs, TwoQubit.Allowed Γ g) ∧
      cs.length ≤ 3 * n * (TwoQubit.cost gs + 1) + TwoQubit.cost gs ∧
      ∀ a, TwoQubit.run cs a = TwoQubit.run gs a := by
  obtain ⟨f, cs, hc, ha, hl, hr⟩ := normalize_head Γ gs h
  refine ⟨localLayer f ++ cs, ?_, List.forall_mem_append.mpr ⟨local_allowed Γ f, ha⟩, ?_, ?_⟩
  · rw [TwoQubit.cost_append, local_cost, Nat.zero_add, hc]
  · have hf := FreeLayers.layer_length f
    simp only [List.length_append, localLayer, List.length_map]
    nlinarith
  · intro a
    rw [TwoQubit.run_append, local_run, hr]

private theorem run_append (gs ss : List (StepWithSwap n)) (a : Circuit.Tableau n) :
    StepWithSwap.run (gs ++ ss) a = StepWithSwap.run ss (StepWithSwap.run gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => cases g <;> exact ih _

private theorem cost_append (gs ss : List (StepWithSwap n)) :
    StepWithSwap.cost (gs ++ ss) = StepWithSwap.cost gs + StepWithSwap.cost ss := by
  induction gs with
  | nil => simp [StepWithSwap.cost]
  | cons g gs ih => cases g <;> simp [StepWithSwap.cost, ih, Nat.add_assoc]

private def swapTail (ss : List (Fin n × Fin n)) : List (StepWithSwap n) :=
  ss.map (fun ij => .swap ij.1 ij.2)

private theorem swapTail_cost (ss : List (Fin n × Fin n)) : StepWithSwap.cost (swapTail ss) = 0 := by
  induction ss with
  | nil => rfl
  | cons ij ss ih => exact ih

private theorem swapTail_run (ss : List (Fin n × Fin n)) (a : Circuit.Tableau n) :
    StepWithSwap.run (swapTail ss) a =
      FreeSwaps.execute (ss.map (fun ij => FreeSwaps.Step.swap ij.1 ij.2)) a := by
  induction ss generalizing a with
  | nil => rfl
  | cons ij ss ih => exact ih _

theorem shorten (Γ : Set TwoQubit.Gate) (swaps : Bool) (gs : List (StepWithSwap n))
    (ha : ∀ g ∈ gs, Allowed Γ swaps g) :
    ∃ ss : List (StepWithSwap n), (∀ g ∈ ss, Allowed Γ swaps g) ∧
      StepWithSwap.cost ss = StepWithSwap.cost gs ∧
      (∀ a, StepWithSwap.run ss a = StepWithSwap.run gs a) ∧
      ss.length ≤ 3 * n * (StepWithSwap.cost gs + 1) + StepWithSwap.cost gs + n := by
  obtain ⟨p, cs, hc, ha, hp, hr⟩ := separate_swaps Γ swaps gs ha
  obtain ⟨ds, hd, had, hl, hrd⟩ := normalize_local Γ cs ha
  have hs : ∃ ss : List (Fin n × Fin n), ss.length ≤ n ∧
      (ss.map (fun ij => Equiv.swap ij.1 ij.2)).prod = p ∧
      (∀ g ∈ swapTail ss, Allowed Γ swaps g) := by
    rcases hp with h | rfl
    · obtain ⟨ss, hl, hs⟩ := FreeSwaps.short_swap_word p
      refine ⟨ss, hl, hs, ?_⟩
      intro g hg
      obtain ⟨ij, hg, rfl⟩ := List.mem_map.mp hg
      exact h
    · exact ⟨[], Nat.zero_le _, rfl, by simp [swapTail]⟩
  obtain ⟨ss, hs, hperm, hsa⟩ := hs
  refine ⟨ds.map StepWithSwap.gate ++ swapTail ss,
    List.forall_mem_append.mpr ⟨(allowed_embed Γ swaps ds).mpr had, hsa⟩, ?_, ?_, ?_⟩
  · rw [cost_append, StepWithSwap.cost_gates, swapTail_cost, Nat.add_zero, hd, hc]
  · intro a
    rw [run_append, StepWithSwap.run_gates, swapTail_run, FreeSwaps.execute_swap_word, hperm, hrd, hr]
  · simp only [List.length_append, List.length_map, swapTail]
    rw [hc] at hl
    exact Nat.add_le_add hl hs

theorem bounded_certificate (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ)
    (swaps : Bool) (target : Circuit.Tableau n) (k : Nat)
    (gs : List (StepWithSwap n)) (ha : ∀ g ∈ gs, Allowed Γ swaps g)
    (hk : StepWithSwap.cost gs ≤ k)
    (ht : Circuit.Same (StepWithSwap.run gs (Circuit.identity n)) target) :
    ∃ ss : List (StepWithSwap n), (∀ g ∈ ss, Allowed Γ swaps g) ∧ StepWithSwap.cost ss ≤ k ∧
      Circuit.Same (StepWithSwap.run ss (Circuit.identity n)) target ∧
      ss.length ≤ 3 * n * (n ^ 2 + 1) + n ^ 2 + n := by
  have hcap : ∃ ds : List (StepWithSwap n), (∀ g ∈ ds, Allowed Γ swaps g) ∧
      StepWithSwap.cost ds ≤ min k (n ^ 2) ∧
      Circuit.Same (StepWithSwap.run ds (Circuit.identity n)) target := by
    rcases le_total k (n ^ 2) with h | h
    · exact ⟨gs, ha, by rwa [min_eq_left h], ht⟩
    · have heq : StepWithSwap.run gs (Circuit.identity n) = target := by
        apply FreeLayers.tableau_ext
        intro i j
        exact Prod.ext (ht i j).1 (ht i j).2
      have hsp : Circuit.ColumnsSymplectic target :=
        heq ▸ StepWithSwap.columnsSymplectic_run (Circuit.columnsSymplectic_identity n) gs
      obtain ⟨ds, hd, hr⟩ := TwoQubit.from_circuit Γ supports target _
        (Circuit.full_synthesis_bound_of_symplectic target hsp)
      refine ⟨ds.map StepWithSwap.gate, (allowed_embed Γ swaps ds).mpr hd, ?_, ?_⟩
      · rw [StepWithSwap.cost_gates, min_eq_right h]
        exact hr.1
      · rw [StepWithSwap.run_gates]
        exact hr.2
  obtain ⟨ds, ha, hc, ht⟩ := hcap
  obtain ⟨ss, ha, he, hr, hl⟩ := shorten Γ swaps ds ha
  refine ⟨ss, ha, he.trans_le (hc.trans (min_le_left _ _)), by rwa [hr], hl.trans ?_⟩
  have hc' := hc.trans (min_le_right _ _)
  gcongr

end CliffordFrontier.FullVerifier
