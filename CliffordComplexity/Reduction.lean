/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.Program
public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Reduction

Combinators for certified many-one reductions built from `Code`.
`CertifiedReduction.polyTimeReducible` exposes their Frontier complexity statements.
-/

@[expose] public section

namespace CliffordComplexity

/-- A decision problem represented by a predicate on its instances. -/
abbrev Problem (α : Type) := α → Prop

/-- Restrict the yes-instances to those satisfying an additional predicate. -/
def Problem.restrict {α : Type} (p guard : Problem α) : Problem α :=
  fun x => guard x ∧ p x

/-- A many-one map with its correctness equivalence. -/
structure Reduction {α β : Type} (p : Problem α) (q : Problem β) where
  /-- Translate a source instance to a target instance. -/
  map : α → β
  /-- The map preserves and reflects membership. -/
  correct : ∀ x, p x ↔ q (map x)

infixr:25 " ⟶ᵣ " => Reduction

/-- Compose two many-one maps and their correctness equivalences. -/
def Reduction.comp {α β γ : Type} {p : Problem α} {q : Problem β} {r : Problem γ}
    (first : p ⟶ᵣ q) (second : q ⟶ᵣ r) : p ⟶ᵣ r :=
  ⟨second.map ∘ first.map, fun x => (first.correct x).trans (second.correct _)⟩

/-- A polynomial-time program with a proof of the many-one reduction equivalence. -/
structure CertifiedReduction {s t : Ty} (source : Problem s.denote) (target : Problem t.denote) where
  /-- The polynomial-time program computing the target instance. -/
  code : Code s t
  /-- The program preserves and reflects membership. -/
  correct : ∀ x, source x ↔ target (code.eval x)

/-- Compose two certified reductions using program composition. -/
def CertifiedReduction.comp {s t u : Ty} {p : Problem s.denote} {q : Problem t.denote}
    {r : Problem u.denote} (first : CertifiedReduction p q) (second : CertifiedReduction q r) :
    CertifiedReduction p r :=
  ⟨.comp first.code second.code, fun x => (first.correct x).trans (second.correct _)⟩

/-- Interpret a certified reduction as a function and its correctness equivalence. -/
def CertifiedReduction.toReduction {s t : Ty} {p : Problem s.denote}
    {q : Problem t.denote} (r : CertifiedReduction p q) : p ⟶ᵣ q := ⟨r.code.eval, r.correct⟩

/-- A certified program gives a reduction in Frontier’s polynomial-time relation. -/
theorem CertifiedReduction.polyTimeReducible {s t : Ty} {p : Problem s.denote}
    {q : Problem t.denote} (r : CertifiedReduction p q) :
    Cslib.Complexity.PolyTimeReducible (encodeTy s) (encodeTy t) {x | p x} {x | q x} :=
  ⟨r.code.eval, r.code.polyTime, r.correct⟩

end CliffordComplexity
