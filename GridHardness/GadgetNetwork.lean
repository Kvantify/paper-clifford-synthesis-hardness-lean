/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.ProductPathCover
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Gadget Network

A finite network of disjoint gadgets with explicitly labelled boundary
links. Cell-to-cell links join distinct cells; each cell's internal graph is
exactly the specified gadget. Hamiltonicity refers to one spanning cycle.
-/

@[expose] public section

namespace GridHardness.GadgetNetwork
open PathCover

section
variable {O C W I : Type*}
variable (outside : O → O → Prop) (inside : W → W → Prop)
variable (input output : I → Bool → W)
variable (enter : O → C → I → Bool → Prop)
variable (leave : C → I → Bool → O → Prop)
variable (link : C → I → Bool → C → I → Bool → Prop)

/-- The vertex set contains the outside vertices and one disjoint copy of
`W` for every cell. Boundary links do not add edges within any cell. -/
def Adj : (O ⊕ (C × W)) → (O ⊕ (C × W)) → Prop
  | Sum.inl a, Sum.inl b => outside a b
  | Sum.inl a, Sum.inr (c, v) => ∃ b s, enter a c b s ∧ v = input b s
  | Sum.inr (c, u), Sum.inl a => ∃ b s, leave c b s a ∧ u = output b s
  | Sum.inr (c, u), Sum.inr (d, v) =>
    (c = d ∧ inside u v) ∨
    (c ≠ d ∧ ∃ b s k t, link c b s d k t ∧ u = output b s ∧ v = input k t)

/-- The common contracted network, independent of the gadget's vertex count. -/
def Wiring (choice : C → I → Bool) :
    (O ⊕ (C × I)) → (O ⊕ (C × I)) → Prop
  | Sum.inl a, Sum.inl b => outside a b
  | Sum.inl a, Sum.inr (c, b) => enter a c b (choice c b)
  | Sum.inr (c, b), Sum.inl a => leave c b (choice c b) a
  | Sum.inr (c, b), Sum.inr (d, k) =>
    c ≠ d ∧ link c b (choice c b) d k (choice d k)

theorem internal (step : Equiv.Perm (O ⊕ (C × W)))
    (ha : ∀ w, Adj outside inside input output enter leave link w (step w))
    (c : C) (u v : W) (h : step (Sum.inr (c, u)) = Sum.inr (c, v)) :
    inside u v := by
  have hh := ha (Sum.inr (c, u))
  rw [h] at hh
  exact (hh.resolve_right (fun h => h.1 rfl)).2

theorem outgoing (step : Equiv.Perm (O ⊕ (C × W)))
    (ha : ∀ w, Adj outside inside input output enter leave link w (step w))
    (c : C) (u : W) (hu : ∀ b s, u ≠ output b s) :
    ∃ v, step (Sum.inr (c, u)) = Sum.inr (c, v) := by
  cases hh : step (Sum.inr (c, u)) with
  | inl o =>
    have h := ha (Sum.inr (c, u))
    rw [hh] at h
    obtain ⟨b, s, _, he⟩ := h
    exact False.elim (hu b s he)
  | inr p =>
    rcases p with ⟨d, v⟩
    have h := ha (Sum.inr (c, u))
    rw [hh] at h
    rcases h with ⟨rfl, _⟩ | ⟨_, b, s, k, t, _, he, _⟩
    · exact ⟨v, rfl⟩
    · exact False.elim (hu b s he)

theorem incoming (step : Equiv.Perm (O ⊕ (C × W)))
    (ha : ∀ w, Adj outside inside input output enter leave link w (step w))
    (c : C) (v : W) (hv : ∀ b s, v ≠ input b s) :
    ∃ u, step (Sum.inr (c, u)) = Sum.inr (c, v) := by
  obtain ⟨w, hw⟩ := step.surjective (Sum.inr (c, v))
  cases w with
  | inl o =>
    have h := ha (Sum.inl o)
    rw [hw] at h
    obtain ⟨b, s, _, he⟩ := h
    exact False.elim (hv b s he)
  | inr p =>
    rcases p with ⟨d, u⟩
    have h := ha (Sum.inr (d, u))
    rw [hw] at h
    rcases h with ⟨rfl, _⟩ | ⟨_, b, s, k, t, _, _, he⟩
    · exact ⟨u, hw⟩
    · exact False.elim (hv k t he)

theorem cell_injective (c : C) :
    Function.Injective (fun w : W => (Sum.inr (c, w) : O ⊕ (C × W))) := by
  intro u v h
  exact congrArg Prod.snd (Sum.inr_injective h)

variable (covers : (I → Bool) → Cover I W)

theorem internalEdges
    (hi : ∀ s, (covers s).InternalEdges inside) (choice : C → I → Bool) :
    ((Cover.family (fun c => covers (choice c))).extend O).InternalEdges
      (Adj outside inside input output enter leave link) := by
  apply Cover.extend_internalEdges
  rintro ⟨c, b⟩ j
  exact Or.inl ⟨rfl, hi (choice c) b j⟩

theorem cover_wiring
    (hinj : Function.Injective (fun p : I × Bool => input p.1 p.2))
    (honj : Function.Injective (fun p : I × Bool => output p.1 p.2))
    (hf : ∀ s b, (covers s).first b = input b (s b))
    (hl : ∀ s b, (covers s).finish b = output b (s b))
    (hn : ∀ b s k t, ¬inside (output b s) (input k t))
    (choice : C → I → Bool) (u v : O ⊕ (C × I)) :
    ((Cover.family (fun c => covers (choice c))).extend O).Wiring
      (Adj outside inside input output enter leave link) u v ↔
    Wiring outside enter leave link choice u v := by
  cases u with
  | inl a =>
    cases v with
    | inl b => rfl
    | inr p =>
      rcases p with ⟨c, b⟩
      change (∃ k t, enter a c k t ∧ (covers (choice c)).first b = input k t) ↔ _
      rw [hf]
      constructor
      · rintro ⟨k, t, h, he⟩
        have hp : (b, choice c b) = (k, t) := hinj he
        cases hp
        exact h
      · intro h
        exact ⟨b, choice c b, h, rfl⟩
  | inr p =>
    rcases p with ⟨c, b⟩
    cases v with
    | inl a =>
      change (∃ k t, leave c k t a ∧ (covers (choice c)).finish b = output k t) ↔ _
      rw [hl]
      constructor
      · rintro ⟨k, t, h, he⟩
        have hp : (b, choice c b) = (k, t) := honj he
        cases hp
        exact h
      · intro h
        exact ⟨b, choice c b, h, rfl⟩
    | inr p =>
      rcases p with ⟨d, k⟩
      change ((c = d ∧ inside ((covers (choice c)).finish b) ((covers (choice d)).first k)) ∨
        (c ≠ d ∧ ∃ b' s k' t, link c b' s d k' t ∧
          (covers (choice c)).finish b = output b' s ∧
          (covers (choice d)).first k = input k' t)) ↔ _
      rw [hl, hf]
      simp only [hn, and_false, false_or]
      constructor
      · rintro ⟨hcd, b', s, k', t, h, he, he'⟩
        have hp : (b, choice c b) = (b', s) := honj he
        have hq : (k, choice d k) = (k', t) := hinj he'
        cases hp
        cases hq
        exact ⟨hcd, h⟩
      · rintro ⟨hcd, h⟩
        exact ⟨hcd, b, choice c b, k, choice d k, h, rfl, rfl⟩

/-- The hypotheses concern the fixed gadget only. In applications the route
classification is proved from its actual incident edges, then instantiated in
every cell of this concrete graph. -/
theorem hamiltonian_iff_wiring [Finite O] [Finite C] [Finite I]
    (hinj : Function.Injective (fun p : I × Bool => input p.1 p.2))
    (honj : Function.Injective (fun p : I × Bool => output p.1 p.2))
    (hf : ∀ s b, (covers s).first b = input b (s b))
    (hl : ∀ s b, (covers s).finish b = output b (s b))
    (hn : ∀ b s k t, ¬inside (output b s) (input k t))
    (hi : ∀ s, (covers s).InternalEdges inside)
    (classify : ∀ (step : Equiv.Perm (O ⊕ (C × W))), OneOrbit step →
      (∀ w, Adj outside inside input output enter leave link w (step w)) →
      ∀ c, ∃ s, (covers s).InternalEdges
        (fun u v => step (Sum.inr (c, u)) = Sum.inr (c, v))) :
    Hamiltonian (Adj outside inside input output enter leave link) ↔
      ∃ choice : C → I → Bool, Hamiltonian (Wiring outside enter leave link choice) := by
  classical
  rw [PathCover.hamiltonian_iff_wiring
    (fun choice : C → I → Bool => (Cover.family (fun c => covers (choice c))).extend O)
    (Adj outside inside input output enter leave link)
    (internalEdges outside inside input output enter leave link covers hi) (by
      intro step ho ha
      choose choice hc using classify step ho ha
      refine ⟨choice, Cover.extend_followedBy _ step ?_⟩
      rintro ⟨c, b⟩ j
      exact hc c b j)]
  apply exists_congr
  intro choice
  unfold Hamiltonian
  apply exists_congr
  intro step
  exact and_congr_right (fun _ => forall_congr' (fun u =>
    cover_wiring outside inside input output enter leave link covers hinj honj hf hl hn
      choice u (step u)))

end
end GridHardness.GadgetNetwork
