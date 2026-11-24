/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRouting
public import GridHardness.XorLineScheduleBundleTransport

/-!
# SAT Crossing Horizontal Interface

The genuine interface left after the next insertion removes section zero
of a previous crossing. Forty old vertices survive; their two edges to the
new crossing use the false ports, not the true ports of a second complete
48-vertex tile.
-/

@[expose] public section

namespace GridHardness.SatCrossingHorizontal
open XorLine XorLineSchedule
set_option autoImplicit false

/-- The vertices retained when section zero is refreshed by the next move. -/
def Retained : XorLine.Vertex 4 → Prop
  | .inl (i,_) => i≠0
  | .inr _ => True

instance (v : XorLine.Vertex 4) : Decidable (Retained v) := by
  cases v with
  | inl v => exact inferInstanceAs (Decidable (v.1≠0))
  | inr v => exact isTrue trivial

abbrev RetainedVertex := {v : XorLine.Vertex 4 // Retained v}

theorem retained_count : Fintype.card RetainedVertex=40 := by decide

theorem retained_ne_zero (v : RetainedVertex) (j : Fin 8) : x (0 : Fin 5) j≠v.val := by
  intro h
  have hv := v.property
  rw [← h] at hv
  exact hv rfl

/-- The old row-zero input is the only retained vertex entering section zero. -/
theorem retained_enter : ∀ (v : XorLine.Vertex 4), Retained v → ∀ j : Fin 8,
    Adj 4 v (x 0 j) ↔ v=row 0 false ∧ j=4 := by decide +kernel

/-- The old row-zero output is the only retained vertex receiving section zero. -/
theorem retained_leave : ∀ (v : XorLine.Vertex 4), Retained v → ∀ j : Fin 8,
    Adj 4 (x 0 j) v ↔ v=row 0 true ∧ j=7 := by decide +kernel

section
variable {V : Type*} {D : V → V → Prop} (b : Bundle D 4)
variable (f : XorLine.Vertex 4 → V) (hf : Function.Injective f)

/-- Explicit surviving identities in the actual marked replacement. -/
def kept (v : RetainedVertex) : b.RefinedVertex (fun j => f (x 0 j)) :=
  .inl ⟨.inl (f v.val),Bundle.old_not_in_sourceMarker _ _
    (fun j h => retained_ne_zero v j (hf h))⟩

theorem kept_injective : Function.Injective (kept b f hf) := by
  intro u v h
  apply Subtype.ext
  exact hf (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj h)))

/-- Exact incoming interface with the next refined crossing. The assumptions
say only that the old tile embeds in the ambient graph and that the newly
crossed bundle is elsewhere. No Hamiltonian-cycle condition is assumed. -/
theorem incoming_interface
    (ha : ∀ u v, D (f u) (f v) ↔ Adj 4 u v)
    (hs : ∀ i v, f v ≠b.source i) (ht : ∀ i v, f v ≠b.target i)
    (u : RetainedVertex) (v : XorLine.Vertex 4) :
    b.refined (fun j => f (x 0 j)) (kept b f hf u) (.inr v) ↔
      u.val=row 0 false ∧ v=inputPort 4 (.inl false) := by
  change (∃ p, Subdivision.Adj D b.source b.target (.inl (f u.val))
    (sourceMarker (fun j => f (x 0 j)) (Source.inputPort 4 p)) ∧ v=inputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,hv⟩
    cases p with
    | inl side =>
      cases side
      · have hh := (retained_enter u.val u.property 4).mp ((ha _ _).mp hp.1)
        exact ⟨hh.1,hv⟩
      · have hh := (retained_enter u.val u.property 3).mp ((ha _ _).mp hp.1)
        exact False.elim (by simpa using hh.2)
    | inr i => exact False.elim (hs i u.val hp.1)
  · rintro ⟨hu,hv⟩
    refine ⟨.inl false,⟨?_,?_⟩,hv⟩
    · apply (ha _ _).mpr
      exact (retained_enter u.val u.property 4).mpr ⟨hu,rfl⟩
    · rintro ⟨i,_,hi⟩
      exact ht i (x 0 4) hi

theorem outgoing_interface
    (ha : ∀ u v, D (f u) (f v) ↔ Adj 4 u v)
    (hs : ∀ i v, f v ≠b.source i) (ht : ∀ i v, f v ≠b.target i)
    (u : RetainedVertex) (v : XorLine.Vertex 4) :
    b.refined (fun j => f (x 0 j)) (.inr v) (kept b f hf u) ↔
      v=outputPort 4 (.inl false) ∧ u.val=row 0 true := by
  change (∃ p, Subdivision.Adj D b.source b.target
    (sourceMarker (fun j => f (x 0 j)) (Source.outputPort 4 p))
    (.inl (f u.val)) ∧ v=outputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,hv⟩
    cases p with
    | inl side =>
      cases side
      · have hh := (retained_leave u.val u.property 7).mp ((ha _ _).mp hp.1)
        exact ⟨hv,hh.1⟩
      · have hh := (retained_leave u.val u.property 0).mp ((ha _ _).mp hp.1)
        exact False.elim (by simpa using hh.2)
    | inr i => exact False.elim (ht i u.val hp.2)
  · rintro ⟨hv,hu⟩
    refine ⟨.inl false,⟨?_,?_⟩,hv⟩
    · apply (ha _ _).mpr
      exact (retained_leave u.val u.property 7).mpr ⟨hu,rfl⟩
    · rintro ⟨i,hi,_⟩
      exact hs i (x 0 7) hi

end
end GridHardness.SatCrossingHorizontal
