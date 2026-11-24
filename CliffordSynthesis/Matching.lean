/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Option
public import Mathlib.Tactic

/-!
# Matching

Partial matchings for the untouched hidden pairs. Erasing the
pairs meeting two endpoints affects at most four physical wires.
-/

@[expose] public section

namespace CliffordSynthesis.Matching

variable {n : Nat}

structure State (n : Nat) where
  mate : Fin n → Option (Fin n)
  distinct : ∀ i j, mate i = some j → i ≠ j
  symmetric : ∀ i j, mate i = some j → mate j = some i

def empty (n : Nat) : State n where
  mate _ := none
  distinct _ _ h := by contradiction
  symmetric _ _ h := by contradiction

def affected (m : State n) (c t : Fin n) : Finset (Fin n) :=
  {c, t} ∪ (m.mate c).toFinset ∪ (m.mate t).toFinset

theorem mem_affected (m : State n) (c t i : Fin n) :
    i ∈ affected m c t ↔ i = c ∨ i = t ∨ m.mate c = some i ∨ m.mate t = some i := by
  simp [affected]

theorem affected_partner (m : State n) (c t i j : Fin n) (hij : m.mate i = some j) :
    i ∈ affected m c t ↔ j ∈ affected m c t := by
  have one (i j : Fin n) (hij : m.mate i = some j) (hi : i ∈ affected m c t) :
      j ∈ affected m c t := by
    rw [mem_affected] at hi ⊢
    rcases hi with rfl | rfl | hci | hti
    · exact Or.inr (Or.inr (Or.inl hij))
    · exact Or.inr (Or.inr (Or.inr hij))
    · have hjc : j = c := Option.some.inj (hij.symm.trans (m.symmetric c i hci))
      exact Or.inl hjc
    · have hjt : j = t := Option.some.inj (hij.symm.trans (m.symmetric t i hti))
      exact Or.inr (Or.inl hjt)
  exact ⟨one i j hij, one j i (m.symmetric i j hij)⟩

theorem affected_card (m : State n) (c t : Fin n) : (affected m c t).card ≤ 4 := by
  have hc : (m.mate c).toFinset.card ≤ 1 := by cases m.mate c <;> simp
  have ht : (m.mate t).toFinset.card ≤ 1 := by cases m.mate t <;> simp
  have h₁ := Finset.card_union_le ({c, t} ∪ (m.mate c).toFinset) (m.mate t).toFinset
  have h₂ := Finset.card_union_le {c, t} (m.mate c).toFinset
  have h₃ : ({c, t} : Finset (Fin n)).card ≤ 2 := by
    by_cases hct : c = t <;> simp [hct]
  dsimp [affected]
  omega

def erase (m : State n) (c t : Fin n) : State n where
  mate i := if i ∈ affected m c t then none else m.mate i
  distinct i j h := by
    split_ifs at h with hi
    exact m.distinct i j h
  symmetric i j h := by
    split_ifs at h with hi
    rw [ite_eq_right (fun hj => hi ((affected_partner m c t i j h).mpr hj))]
    exact m.symmetric i j h

theorem erase_mate (m : State n) (c t i : Fin n) :
    (erase m c t).mate i = if i ∈ affected m c t then none else m.mate i := rfl

theorem erase_left (m : State n) (c t : Fin n) : (erase m c t).mate c = none := by
  simp [erase, mem_affected]

theorem erase_right (m : State n) (c t : Fin n) : (erase m c t).mate t = none := by
  simp [erase, mem_affected]

theorem erase_some (m : State n) (c t i j : Fin n)
    (h : (erase m c t).mate i = some j) :
    m.mate i = some j ∧ i ≠ c ∧ i ≠ t ∧ j ≠ c ∧ j ≠ t := by
  rw [erase_mate] at h
  split_ifs at h with hi
  have hj : j ∉ affected m c t := fun hj => hi ((affected_partner m c t i j h).mpr hj)
  simp only [mem_affected, not_or] at hi hj
  exact ⟨h, hi.1, hi.2.1, hj.1, hj.2.1⟩

/-- Add a new pair at two currently unpaired, distinct endpoints. -/
def insert (m : State n) (c t : Fin n) (hct : c ≠ t)
    (hc : m.mate c = none) (ht : m.mate t = none) : State n where
  mate i := if i = c then some t else if i = t then some c else m.mate i
  distinct i j h := by
    split_ifs at h with hi hi
    · have h' : t = j := Option.some.inj h
      simpa [← hi, h'] using hct
    · have h' : c = j := Option.some.inj h
      simpa [← hi, h'] using Ne.symm hct
    · exact m.distinct i j h
  symmetric i j h := by
    split_ifs at h with hi hi
    · have h' : t = j := Option.some.inj h
      subst i; subst j
      simp [Ne.symm hct]
    · have h' : c = j := Option.some.inj h
      subst i; subst j
      simp
    · have hjc : j ≠ c := by
        intro hj
        have hh := m.symmetric i j h
        simp [hj, hc] at hh
      have hjt : j ≠ t := by
        intro hj
        have hh := m.symmetric i j h
        simp [hj, ht] at hh
      simp [hjc, hjt, m.symmetric i j h]

theorem insert_mate (m : State n) (c t i : Fin n) (hct : c ≠ t)
    (hc : m.mate c = none) (ht : m.mate t = none) :
    (insert m c t hct hc ht).mate i =
      if i = c then some t else if i = t then some c else m.mate i := rfl

end CliffordSynthesis.Matching
