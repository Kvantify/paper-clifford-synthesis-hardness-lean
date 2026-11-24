/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.TwoQubitCircuits

/-!
# Gate Families

Any fixed gate family containing a locally CNOT-equivalent gate supports
the forward reduction with one paid gate per CNOT.
-/

@[expose] public section

namespace CliffordSynthesis.TwoQubit

variable {n : Nat}

def Allowed (Γ : Set Gate) : Step n → Prop
  | .H _ | .S _ => True
  | .two _ _ _ g => g ∈ Γ

def SynthesizesFrom (Γ : Set Gate) (target : Circuit.Tableau n) (k : Nat) : Prop :=
  ∃ gs : List (Step n), (∀ g ∈ gs, Allowed Γ g) ∧ cost gs ≤ k ∧
    Circuit.Same (run gs (Circuit.identity n)) target

/-- Local equivalence as equality of the actual four-bit linear actions. -/
def LocallyCNOT (g : Gate) : Prop :=
  ∃ b₀ b₁ a₀ a₁ : Fin 6, ∀ v : Bits,
    localAction a₀ a₁ (action g.val (localAction b₀ b₁ v)) = cnotAction v

def SupportsCNOT (Γ : Set Gate) : Prop := ∃ g ∈ Γ, LocallyCNOT g

theorem zero_cost_allowed (Γ : Set Gate) (gs : List (Step n)) (h : cost gs = 0) :
    ∀ g ∈ gs, Allowed Γ g := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh : paid g = 0 ∧ cost gs = 0 := Nat.add_eq_zero_iff.mp h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · cases s <;> simp_all [paid, Allowed]
    · exact ih hh.2 s hs

/-- Replace a CNOT by free local layers and one gate from Γ. -/
theorem simulate_cnot (Γ : Set Gate) (hΓ : SupportsCNOT Γ)
    (c t : Fin n) (hct : c ≠ t) :
    ∃ gs : List (Step n), (∀ g ∈ gs, Allowed Γ g) ∧ cost gs = 1 ∧
      ∀ a, run gs a = Circuit.cnot c t a := by
  obtain ⟨g, hg, b₀, b₁, a₀, a₁, he⟩ := hΓ
  let before := (localWord c t b₀ b₁).map ofGate
  let after := (localWord c t a₀ a₁).map ofGate
  have hb : cost before = 0 := (ofGate_cost _).trans (localWord_cost _ _ _ _)
  have ha : cost after = 0 := (ofGate_cost _).trans (localWord_cost _ _ _ _)
  refine ⟨before ++ .two c t hct g :: after, ?_, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact zero_cost_allowed Γ before hb s hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact hg
      · exact zero_cost_allowed Γ after ha s hs
  · simp [cost_append, cost, paid, hb, ha]
  · intro a
    rw [run_append]
    change run after (update c t (action g.val) (run before a)) = _
    simp only [before, after, ofGate_run, localWord_run c t hct, update_comp c t hct]
    rw [cnot_update c t hct]
    congr 1
    exact funext he

/-- Uniform replacement works for the entire circuit and every input tableau. -/
theorem simulate_circuit (Γ : Set Gate) (hΓ : SupportsCNOT Γ) (cs : List (Circuit.Gate n)) :
    ∃ gs : List (Step n), (∀ g ∈ gs, Allowed Γ g) ∧ cost gs = Circuit.cost cs ∧
      ∀ a, run gs a = Circuit.run cs a := by
  induction cs with
  | nil => exact ⟨[], by simp, rfl, fun _ => rfl⟩
  | cons g cs ih =>
    obtain ⟨gs, ha, hc, hr⟩ := ih
    cases g with
    | H i =>
      refine ⟨.H i :: gs, ?_, by simpa [cost, paid, Circuit.cost, Circuit.paid] using hc, fun a => hr (Circuit.hadamard i a)⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · trivial
      · exact ha s hs
    | S i =>
      refine ⟨.S i :: gs, ?_, by simpa [cost, paid, Circuit.cost, Circuit.paid] using hc, fun a => hr (Circuit.phase i a)⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · trivial
      · exact ha s hs
    | CX c t hct =>
      obtain ⟨pre, hp, hpc, hpr⟩ := simulate_cnot Γ hΓ c t hct
      refine ⟨pre ++ gs, ?_, ?_, ?_⟩
      · intro s hs
        exact (List.mem_append.mp hs).elim (hp s) (ha s)
      · rw [cost_append, hpc, hc]
        rfl
      · intro a
        rw [run_append, hpr, hr]
        rfl

theorem from_circuit (Γ : Set Gate) (hΓ : SupportsCNOT Γ) (target : Circuit.Tableau n) (k : Nat)
    (h : Circuit.SynthesizesWithin target k) : SynthesizesFrom Γ target k := by
  obtain ⟨cs, hk, hs⟩ := h
  obtain ⟨gs, ha, hc, hr⟩ := simulate_circuit Γ hΓ cs
  exact ⟨gs, ha, by rwa [hc], by rwa [hr]⟩

theorem cnot_locallyCNOT : LocallyCNOT cnotGate := by
  exact ⟨0, 0, 0, 0, cnotGate_action⟩

/-- A gate that is neither local nor local followed by SWAP is entangling. -/
def Entangling (g : Gate) : Prop :=
  ¬∃ f₀ f₁ : Fin 6, ∃ swap : Bool, ∀ v : Bits,
    action g.val v = if swap then swapAction (localAction f₀ f₁ v) else localAction f₀ f₁ v

theorem cnot_entangling : Entangling cnotGate := by unfold Entangling; decide

theorem all_supportsCNOT : SupportsCNOT Set.univ := ⟨cnotGate, Set.mem_univ _, cnot_locallyCNOT⟩
theorem entangling_supportsCNOT : SupportsCNOT {g | Entangling g} :=
  ⟨cnotGate, cnot_entangling, cnot_locallyCNOT⟩

end CliffordSynthesis.TwoQubit
