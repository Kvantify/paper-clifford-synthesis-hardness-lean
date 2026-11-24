/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Std

/-!
# Arithmetic

Elementary arithmetic proved without foundational axioms.
Some standard-library cancellation lemmas use propositional extensionality;
the versions here allow an empty Comparator axiom whitelist.
-/

public section

namespace CliffordSynthesis.Arithmetic

theorem swap (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, ← Nat.add_assoc b c d, Nat.add_comm b c,
    Nat.add_assoc c b d, ← Nat.add_assoc]

theorem cancelLeft (a b c : Nat) (h : a + b = a + c) : b = c := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.succ.inj h)

theorem cancelRight (a b c : Nat) (h : a + c = b + c) : a = b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact cancelLeft c a b h

theorem leCancelLeft (a b c : Nat) (h : a + b ≤ a + c) : b ≤ c := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  rw [Nat.add_assoc] at hk
  exact Nat.le.intro (cancelLeft a (b + k) c hk)

theorem leCancelRight (a b c : Nat) (h : a + c ≤ b + c) : a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact leCancelLeft c a b h

theorem addSub (a b : Nat) : a + b - a = b := by
  induction a with
  | zero => exact Nat.zero_add b
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_sub_succ]
    exact ih

theorem subAdd (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, addSub]

end CliffordSynthesis.Arithmetic
