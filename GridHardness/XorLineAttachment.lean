/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoPathCover
public import Mathlib.Data.Fintype.Sum

/-!
# XOR Line Attachment

Attach a verified path-cover gadget through an arbitrary type of boundary
ports. This supports a chosen XOR route together with independently mandatory
row routes, whose ports have different index types.
-/

@[expose] public section

set_option autoImplicit false

namespace GridHardness.XorLineAttachment
open PathCover

def Adj {O W P : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop) :
    (O ⊕ W) → (O ⊕ W) → Prop
  | .inl a, .inl b => outside a b
  | .inl a, .inr b => ∃ p, enter a p ∧ b = input p
  | .inr a, .inl b => ∃ p, leave p b ∧ a = output p
  | .inr a, .inr b => inside a b

def Wiring {O I P : Type*} (outside : O → O → Prop)
    (enter : O → P → Prop) (leave : P → O → Prop) (selected : I → P) :
    (O ⊕ I) → (O ⊕ I) → Prop
  | .inl a, .inl b => outside a b
  | .inl a, .inr b => enter a (selected b)
  | .inr a, .inl b => leave (selected a) b
  | .inr _, .inr _ => False

theorem internal {O W P : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (u v : W) (h : step (.inr u) = .inr v) : inside u v := by
  have hh := ha (.inr u)
  rwa [h] at hh

theorem outgoing {O W P : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (u : W) (hu : ∀ p, u ≠ output p) : ∃ v, step (.inr u) = .inr v := by
  cases hh : step (.inr u) with
  | inl o =>
    have h := ha (.inr u)
    rw [hh] at h
    obtain ⟨p,_,he⟩ := h
    exact False.elim (hu p he)
  | inr v => exact ⟨v,rfl⟩

theorem incoming {O W P : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop)
    (step : Equiv.Perm (O ⊕ W))
    (ha : ∀ w, Adj outside inside input output enter leave w (step w))
    (v : W) (hv : ∀ p, v ≠ input p) : ∃ u, step (.inr u) = .inr v := by
  obtain ⟨u,hu⟩ := step.surjective (.inr v)
  cases u with
  | inl o =>
    have h := ha (.inl o)
    rw [hu] at h
    obtain ⟨p,_,he⟩ := h
    exact False.elim (hv p he)
  | inr u => exact ⟨u,hu⟩

/-- Contracting a verified route cover gives precisely its selected boundary
ports. No adjacency between a selected exit and selected entry may bypass
the outside graph. -/
theorem cover_wiring {O W I P : Type*} (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop)
    (hinj : Function.Injective input) (honj : Function.Injective output)
    (selected : I → P) (c : Cover I W)
    (hf : ∀ i, c.first i = input (selected i))
    (hl : ∀ i, c.finish i = output (selected i))
    (hn : ∀ i j, ¬inside (output (selected i)) (input (selected j)))
    (u v : O ⊕ I) :
    (c.extend O).Wiring (Adj outside inside input output enter leave) u v ↔
      Wiring outside enter leave selected u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => rfl
    | inr v =>
      change (∃ p, enter u p ∧ c.first v = input p) ↔ enter u (selected v)
      rw [hf]
      constructor
      · rintro ⟨p,h,he⟩
        exact (hinj he).symm ▸ h
      · intro h
        exact ⟨selected v,h,rfl⟩
  | inr u =>
    cases v with
    | inl v =>
      change (∃ p, leave p v ∧ c.finish u = output p) ↔ leave (selected u) v
      rw [hl]
      constructor
      · rintro ⟨p,h,he⟩
        exact (honj he).symm ▸ h
      · intro h
        exact ⟨selected u,h,rfl⟩
    | inr v =>
      change inside (c.finish u) (c.first v) ↔ False
      rw [hl,hf]
      exact iff_false_intro (hn u v)

/-- Exact ambient Hamiltonicity from internal route classification. The
classification is proved by each concrete gadget from its own actual edges;
this theorem preserves the single global spanning orbit while contracting it. -/
theorem hamiltonian_iff_wiring {O W I P S : Type*} [Finite O] [Finite I]
    (outside : O → O → Prop) (inside : W → W → Prop)
    (input output : P → W) (enter : O → P → Prop) (leave : P → O → Prop)
    (covers : S → Cover I W) (selected : S → I → P)
    (hinj : Function.Injective input) (honj : Function.Injective output)
    (hf : ∀ s i, (covers s).first i = input (selected s i))
    (hl : ∀ s i, (covers s).finish i = output (selected s i))
    (hn : ∀ s i j, ¬inside (output (selected s i)) (input (selected s j)))
    (hi : ∀ s, (covers s).InternalEdges inside)
    (classify : ∀ step : Equiv.Perm (O ⊕ W), OneOrbit step →
      (∀ w, Adj outside inside input output enter leave w (step w)) →
      ∃ s, (covers s).InternalEdges (fun u v => step (.inr u) = .inr v)) :
    Hamiltonian (Adj outside inside input output enter leave) ↔
      ∃ s, Hamiltonian (Wiring outside enter leave (selected s)) := by
  classical
  let : Fintype O := Fintype.ofFinite O
  let : Fintype I := Fintype.ofFinite I
  have he : ∀ s, ((covers s).extend O).InternalEdges
      (Adj outside inside input output enter leave) := by
    intro s
    exact (covers s).extend_internalEdges _ (hi s)
  have hc : ∀ step : Equiv.Perm (O ⊕ W), OneOrbit step →
      (∀ w, Adj outside inside input output enter leave w (step w)) →
      ∃ s, ((covers s).extend O).FollowedBy step := by
    intro step ho ha
    obtain ⟨s,hs⟩ := classify step ho ha
    exact ⟨s,(covers s).extend_followedBy step hs⟩
  rw [PathCover.hamiltonian_iff_wiring (fun s => (covers s).extend O)
    (Adj outside inside input output enter leave) he hc]
  apply exists_congr
  intro s
  unfold Hamiltonian
  apply exists_congr
  intro step
  exact and_congr_right (fun _ => forall_congr' (fun u =>
    cover_wiring outside inside input output enter leave hinj honj (selected s) (covers s)
      (hf s) (hl s) (hn s) u (step u)))

end GridHardness.XorLineAttachment
