/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Arithmetic

/-!
# Ledger

The amortized appearance ledger, for histories obeying the local table.
`Run` accounts for the unchanged wires at each step. The construction of this
trace from an actual Clifford circuit is proved in CircuitLedger.
-/

@[expose] public section

namespace CliffordSynthesis.Ledger

open Arithmetic

inductive Event where
  | T | D | U | P | M | Z₂ | Z₁ | Z₀
  deriving DecidableEq, Repr

def Event.before : Event → Nat
  | .T => 2
  | .D => 2
  | .U => 0
  | .P => 0
  | .M => 1
  | .Z₂ => 2
  | .Z₁ => 1
  | .Z₀ => 0

def Event.after : Event → Nat
  | .T => 2
  | .D => 0
  | .U => 2
  | .P => 1
  | .M => 0
  | .Z₂ => 2
  | .Z₁ => 1
  | .Z₀ => 0

def Event.births : Event → Nat
  | .T => 1
  | .D => 0
  | .U => 2
  | .P => 1
  | .M => 0
  | .Z₂ => 0
  | .Z₁ => 0
  | .Z₀ => 0

def Event.penalty : Event → Nat
  | .T => 0
  | .D => 0
  | .U => 0
  | .P => 1
  | .M => 1
  | .Z₂ => 2
  | .Z₁ => 2
  | .Z₀ => 2

def Event.exceptional : Event → Nat
  | .T => 0
  | .D => 0
  | .U => 0
  | .P => 1
  | .M => 1
  | .Z₂ => 1
  | .Z₁ => 1
  | .Z₀ => 1

theorem event_balance (e : Event) :
    2 + e.after = 2 * e.births + e.before + e.penalty := by
  cases e <;> rfl

theorem event_exceptional_le (e : Event) : e.exceptional ≤ e.penalty := by
  cases e <;> decide

def births : List Event → Nat
  | [] => 0
  | e :: es => e.births + births es

def penalty : List Event → Nat
  | [] => 0
  | e :: es => e.penalty + penalty es

def exceptional : List Event → Nat
  | [] => 0
  | e :: es => e.exceptional + exceptional es

/-- The possible additions to the marked hidden set: three at M and four at
Z. A P gate instead removes one mark. -/
def Event.markCharge : Event → Nat
  | .M => 3
  | .Z₂ | .Z₁ | .Z₀ => 4
  | _ => 0

def markCharge : List Event → Nat
  | [] => 0
  | e :: es => e.markCharge + markCharge es

def countM (es : List Event) : Nat := es.count .M

def countZ (es : List Event) : Nat := es.count .Z₂ + es.count .Z₁ + es.count .Z₀

/-- The potential charge is exactly the 3M + 4Z. -/
theorem markCharge_eq (es : List Event) : markCharge es = 3 * countM es + 4 * countZ es := by
  induction es with
  | nil => simp [markCharge, countM, countZ]
  | cons e es ih =>
    simp only [countM, countZ] at ih ⊢
    cases e <;> simp [markCharge, Event.markCharge, ih, Nat.mul_add] <;> omega

theorem markCharge_le_penalty (es : List Event) : markCharge es ≤ 3 * penalty es := by
  induction es with
  | nil => simp [markCharge, penalty]
  | cons e es ih =>
    cases e <;> simp only [markCharge, Event.markCharge, penalty, Event.penalty] <;> omega

/-- A trace with a specified number of visible wires at each boundary.
`untouched` counts visible wires outside the two gate endpoints. -/
inductive Run : Nat → Nat → List Event → Prop
  | nil (n : Nat) : Run n n []
  | cons (e : Event) (untouched : Nat) {n : Nat} {es : List Event}
      (tail : Run (untouched + e.after) n es) :
      Run (untouched + e.before) n (e :: es)

theorem balance {s t : Nat} {es : List Event} (h : Run s t es) :
    2 * es.length + t = 2 * births es + s + penalty es := by
  induction h with
  | nil n => rfl
  | @cons e untouched n es tail ih =>
    change 2 * (es.length + 1) + n =
      2 * (e.births + births es) + (untouched + e.before) +
        (e.penalty + penalty es)
    rw [Nat.mul_add, Nat.mul_one, Nat.add_right_comm (2 * es.length) 2 n, ih]
    rw [Nat.add_assoc (2 * births es) (untouched + e.after) (penalty es),
      Nat.add_assoc (2 * births es), Nat.add_assoc untouched]
    rw [Nat.add_assoc untouched (e.after + penalty es) 2,
      Nat.add_right_comm e.after (penalty es) 2, Nat.add_comm e.after 2,
      event_balance e, Nat.mul_add]
    repeat rw [Nat.add_assoc]
    rw [Nat.add_left_comm untouched (2 * e.births),
      Nat.add_left_comm (2 * births es) (2 * e.births)]

theorem exceptional_le (es : List Event) : exceptional es ≤ penalty es := by
  induction es with
  | nil => exact Nat.le_refl 0
  | cons e es ih =>
    exact Nat.add_le_add (event_exceptional_le e) ih

/-- The B ≤ L, doubled ledger identity, and h ≤ 2(L-B).
The doubled form avoids rational division and truncated subtraction errors. -/
theorem amortized {n : Nat} {es : List Event} (h : Run n n es) :
    births es ≤ es.length ∧
    2 * (es.length - births es) = penalty es ∧
    exceptional es ≤ 2 * (es.length - births es) := by
  have hb := balance h
  rw [Nat.add_right_comm (2 * births es) n (penalty es)] at hb
  have hb' := cancelRight _ _ n hb
  have hle : births es ≤ es.length :=
    Nat.le_of_mul_le_mul_left (hb' ▸ Nat.le_add_right (2 * births es) (penalty es))
      (by decide : 0 < 2)
  have hs := subAdd (births es) es.length hle
  have hp : 2 * (es.length - births es) = penalty es := by
    have he := congrArg (fun x => 2 * x) hs
    rw [Nat.mul_add, hb'] at he
    exact cancelLeft _ _ _ he
  exact ⟨hle, hp, hp ▸ exceptional_le es⟩

theorem saturation_no_exceptional {n : Nat} {es : List Event}
    (h : Run n n es) (hs : births es = es.length) :
    exceptional es = 0 := by
  have he := (amortized h).2.2
  rw [hs, Nat.sub_self] at he
  exact Nat.eq_zero_of_le_zero he

end CliffordSynthesis.Ledger
