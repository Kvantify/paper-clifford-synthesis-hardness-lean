/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoPathCover

/-!
# Attached Gadget

Attaching a channel gadget to an arbitrary outside directed graph.
All boundary connections are explicit graph edges. There are no additional
edges between gadget vertices beyond the gadget's own adjacency relation.
-/

@[expose] public section

namespace GridHardness.AttachedGadget
open PathCover

def Adj {O W I : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : I → Bool → W)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop) :
    (O ⊕ W) → (O ⊕ W) → Prop
  | Sum.inl a, Sum.inl b => outside a b
  | Sum.inl a, Sum.inr b => ∃ i s, enter a i s ∧ b = input i s
  | Sum.inr a, Sum.inl b => ∃ i s, leave i s b ∧ a = output i s
  | Sum.inr a, Sum.inr b => inside a b

def Wiring {O I : Type*} (outside : O → O → Prop)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop)
    (choice : I → Bool) : (O ⊕ I) → (O ⊕ I) → Prop
  | Sum.inl a, Sum.inl b => outside a b
  | Sum.inl a, Sum.inr b => enter a b (choice b)
  | Sum.inr a, Sum.inl b => leave a (choice a) b
  | Sum.inr _, Sum.inr _ => False

theorem internal {O W I : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : I → Bool → W)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (u v : W) (h : step (Sum.inr u) = Sum.inr v) : inside u v := by
  have hh := ha (Sum.inr u)
  rwa [h] at hh

theorem outgoing {O W I : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : I → Bool → W)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (u : W) (hu : ∀ i s, u ≠ output i s) : ∃ v, step (Sum.inr u) = Sum.inr v := by
  cases hh : step (Sum.inr u) with
  | inl o =>
    have h := ha (Sum.inr u)
    rw [hh] at h
    obtain ⟨i, s, _, he⟩ := h
    exact False.elim (hu i s he)
  | inr v => exact ⟨v, rfl⟩

theorem incoming {O W I : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : I → Bool → W)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (v : W) (hv : ∀ i s, v ≠ input i s) : ∃ u, step (Sum.inr u) = Sum.inr v := by
  obtain ⟨u, hu⟩ := step.surjective (Sum.inr v)
  cases u with
  | inl o =>
    have h := ha (Sum.inl o)
    rw [hu] at h
    obtain ⟨i, s, _, he⟩ := h
    exact False.elim (hv i s he)
  | inr u => exact ⟨u, hu⟩

/-- After fixing a route choice, the contracted graph depends only on the
outside graph and boundary labels, not the gadget's internal vertex count. -/
theorem cover_wiring {O W I : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : I → Bool → W)
    (enter : O → I → Bool → Prop) (leave : I → Bool → O → Prop)
    (hinj : Function.Injective (fun p : I × Bool => input p.1 p.2))
    (honj : Function.Injective (fun p : I × Bool => output p.1 p.2))
    (choice : I → Bool) (c : Cover I W)
    (hf : ∀ i, c.first i = input i (choice i))
    (hl : ∀ i, c.finish i = output i (choice i))
    (hn : ∀ i j, ¬inside (output i (choice i)) (input j (choice j)))
    (u v : O ⊕ I) :
    (c.extend O).Wiring (Adj outside inside input output enter leave) u v ↔
      Wiring outside enter leave choice u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => rfl
    | inr v =>
      change (∃ i s, enter u i s ∧ c.first v = input i s) ↔ enter u v (choice v)
      rw [hf]
      constructor
      · rintro ⟨i, s, h, he⟩
        have hp : (v, choice v) = (i, s) := hinj he
        cases hp
        exact h
      · intro h
        exact ⟨v, choice v, h, rfl⟩
  | inr u =>
    cases v with
    | inl v =>
      change (∃ i s, leave i s v ∧ c.finish u = output i s) ↔ leave u (choice u) v
      rw [hl]
      constructor
      · rintro ⟨i, s, h, he⟩
        have hp : (u, choice u) = (i, s) := honj he
        cases hp
        exact h
      · intro h
        exact ⟨u, choice u, h, rfl⟩
    | inr v =>
      change inside (c.finish u) (c.first v) ↔ False
      rw [hl, hf]
      exact iff_false_intro (hn u v)

end GridHardness.AttachedGadget
