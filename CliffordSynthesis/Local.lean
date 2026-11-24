/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Std

/-!
# Local

Concrete two-qubit algebra for the effect-of-one-CNOT lemma.
Vectors have bit order x₁,x₂,z₁,z₂. Proofs use kernel reduction,
not native evaluation. The link to arbitrary-dimensional tableaus is
not supplied by this module.
-/

@[expose] public section

namespace CliffordSynthesis.Local

abbrev V := Bool × Bool × Bool × Bool

instance decidableForallV (p : V → Prop) [DecidablePred p] : Decidable (∀ v, p v) :=
  decidable_of_iff (∀ a b c d : Bool, p (a, b, c, d))
    ⟨fun h (a, b, c, d) => h a b c d, fun h a b c d => h (a, b, c, d)⟩

instance (n : Nat) : OfNat V n where
  ofNat := (decide (n % 2 = 1), decide (n / 2 % 2 = 1),
    decide (n / 4 % 2 = 1), decide (n / 8 % 2 = 1))

def add (a b : V) : V :=
  (a.1 ^^ b.1, a.2.1 ^^ b.2.1, a.2.2.1 ^^ b.2.2.1, a.2.2.2 ^^ b.2.2.2)

def sp (a b : V) : Bool :=
  ((a.1 && b.2.2.1) ^^ (a.2.1 && b.2.2.2)) ^^
  ((a.2.2.1 && b.1) ^^ (a.2.2.2 && b.2.1))

def inSpan (a b q : V) : Bool :=
  q == 0 || q == a || q == b || q == add a b

def visible (a b : V) (plane : List V) : Option V :=
  plane.find? (inSpan a b)

def before (a b : V) : Option V × Option V :=
  (visible a b [1, 4, 5], visible a b [2, 8, 10])

def after (a b : V) : Option V × Option V :=
  (visible a b [1, 12, 13], visible a b [3, 8, 11])

def present : Option V → Nat
  | none => 0
  | some _ => 1

def birth (old new : Option V) : Nat :=
  if new.isSome && new != old then 1 else 0

def signature (a b : V) : Nat × Nat × Nat :=
  let old := before a b
  let new := after a b
  (present old.1 + present old.2, present new.1 + present new.2,
    birth old.1 new.1 + birth old.2 new.2)

def permitted (s : Nat × Nat × Nat) : Bool :=
  [(2, 2, 1), (2, 0, 0), (0, 2, 2), (0, 1, 1),
   (1, 0, 0), (2, 2, 0), (1, 1, 0), (0, 0, 0)].contains s

def rowAddition (old new : Option V × Option V) : Bool :=
  old.1.any fun u => old.2.any fun v => new.1.any fun u' => new.2.any fun v' =>
    (u' == u && v' == add u v) || (u' == add u v && v' == v)

def uniqueOn (a b : V) (plane : List V) : Bool :=
  (plane.filter (inSpan a b)).length ≤ 1

-- Kernel evaluation of the finite table needs extra recursion depth.
set_option maxRecDepth 100000 in
theorem localTable : ∀ a b : V, sp a b = false →
    permitted (signature a b) = true := by decide

-- Kernel evaluation of the finite table needs extra recursion depth.
set_option maxRecDepth 100000 in
theorem localRowAddition : ∀ a b : V, sp a b = false →
    signature a b = (2, 2, 1) →
    rowAddition (before a b) (after a b) = true := by decide

-- Kernel evaluation of the finite table needs extra recursion depth.
set_option maxRecDepth 100000 in
theorem localUniqueness : ∀ a b : V, sp a b = false →
    uniqueOn a b [1, 4, 5] = true ∧
    uniqueOn a b [2, 8, 10] = true ∧
    uniqueOn a b [1, 12, 13] = true ∧
    uniqueOn a b [3, 8, 11] = true := by decide

private theorem beqSound : ∀ a b : V, (a == b) = true → a = b := by decide

/-- A two-dimensional binary span cannot provide two distinct vectors
both different from zero and from its two generators. This is the
finite algebra used to exclude fresh returns of an untouched pair. -/
theorem noTwoFresh : ∀ u v p q : V,
    inSpan u v p = true → inSpan u v q = true →
    p ≠ 0 → q ≠ 0 → p ≠ u → p ≠ v → q ≠ u → q ≠ v → p = q := by
  intro u v p q hp hq hp0 hq0 hpu hpv hqu hqv
  have split (a b : Bool) : (a || b) = true → a = true ∨ b = true := by
    cases a <;> cases b <;> decide
  have only (w : V) (hw : inSpan u v w = true)
      (h0 : w ≠ 0) (hu : w ≠ u) (hv : w ≠ v) : w = add u v := by
    rcases split _ _ hw with hab | hlast
    · rcases split _ _ hab with ha | hb
      · rcases split _ _ ha with hz | hu'
        · exact False.elim (h0 (beqSound _ _ hz))
        · exact False.elim (hu (beqSound _ _ hu'))
      · exact False.elim (hv (beqSound _ _ hb))
    · exact beqSound _ _ hlast
  exact (only p hp hp0 hpu hpv).trans (only q hq hq0 hqu hqv).symm

end CliffordSynthesis.Local
