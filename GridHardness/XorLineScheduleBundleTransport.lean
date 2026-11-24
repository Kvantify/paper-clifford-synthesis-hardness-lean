/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleBundle

/-!
# XOR Line Schedule Bundle Transport

Transport every other mandatory bundle through the same concrete move.
Together with `Bundle.after`, this updates an entire registry of crossing arcs.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule.Bundle
open XorLine
variable {V : Type*} {D : V → V → Prop} {m n : Nat}

/-- Other compulsory sources retain their original identities during subdivision. -/
def subdivided (c : Bundle D m) (b : Bundle D n)
    (hs : ∀ i j, c.source i ≠b.source j) : Bundle (Subdivision.Adj D b.source b.target) m where
  source := Sum.inl ∘ c.source
  target := Sum.inl ∘ c.target
  source_injective := Sum.inl_injective.comp c.source_injective
  target_injective := Sum.inl_injective.comp c.target_injective
  edge := by
    intro i
    refine ⟨c.edge i,?_⟩
    rintro ⟨j,hj,_⟩
    exact hs i j hj
  unique := by
    intro i v hv
    rcases v with v | ⟨j,k⟩
    · exact congrArg Sum.inl (c.unique i v hv.1)
    · exact False.elim (hs i j hv.1)

/-- A compulsory arc entirely outside a marked source survives its replacement. -/
def marked (c : Bundle D m) (mark : Source.Vertex n → V)
    (hs : ∀ i, c.source i ∉ Set.range mark)
    (ht : ∀ i, c.target i ∉ Set.range mark) : Bundle (Marked.replacement D mark) m where
  source := fun i => .inl ⟨c.source i,hs i⟩
  target := fun i => .inl ⟨c.target i,ht i⟩
  source_injective := by
    intro i j hij
    exact c.source_injective (congrArg Subtype.val (Sum.inl.inj hij))
  target_injective := by
    intro i j hij
    exact c.target_injective (congrArg Subtype.val (Sum.inl.inj hij))
  edge := c.edge
  unique := by
    intro i v hv
    cases v with
    | inl v => exact congrArg Sum.inl (Subtype.ext (c.unique i v.val hv))
    | inr v =>
      obtain ⟨p,hp,_⟩ := hv
      exact False.elim (ht i ⟨Source.inputPort n p,c.unique i _ hp⟩)

theorem old_not_in_sourceMarker (e : Fin 8 → V) (v : V) (h : ∀ j, e j ≠v) :
    (Sum.inl v : Subdivision.Vertex V (Fin n)) ∉ Set.range (sourceMarker (n := n) e) := by
  rintro ⟨w,hw⟩
  cases w with
  | inl j => exact h j (Sum.inl.inj hw)
  | inr p => contradiction

/-- Concrete update of any other bundle after crossing `b`. The only separation
conditions are on the named original vertices; no post-move hypothesis is needed. -/
def transport (c : Bundle D m) (b : Bundle D n) (e : Fin 8 → V)
    (hs : ∀ i j, c.source i ≠b.source j)
    (hes : ∀ i j, e j ≠c.source i) (het : ∀ i j, e j ≠c.target i) :
    Bundle (b.refined e) m :=
  (c.subdivided b hs).marked (sourceMarker e)
    (fun i => old_not_in_sourceMarker e (c.source i) (hes i))
    (fun i => old_not_in_sourceMarker e (c.target i) (het i))

/-- Residual crossed sources and all transported sources are distinct by their
actual vertex tags, so a registry retains the separation needed for later moves. -/
theorem after_transport_sources (c : Bundle D m) (b : Bundle D n) (e : Fin 8 → V)
    (ht : ∀ i j, e j ≠b.target i) (hs : ∀ i j, c.source i ≠b.source j)
    (hes : ∀ i j, e j ≠c.source i) (het : ∀ i j, e j ≠c.target i)
    (i : Fin n) (j : Fin m) :
    (b.after e ht).source i ≠ (c.transport b e hs hes het).source j := by
  intro h
  cases h

/-- Transport preserves separation between sources of two unaffected bundles. -/
theorem transport_sources_distinct {k : Nat} (c : Bundle D m) (d : Bundle D k)
    (b : Bundle D n) (e : Fin 8 → V)
    (hcs : ∀ i j, c.source i ≠b.source j) (hds : ∀ i j, d.source i ≠b.source j)
    (hecs : ∀ i j, e j ≠c.source i) (hect : ∀ i j, e j ≠c.target i)
    (heds : ∀ i j, e j ≠d.source i) (hedt : ∀ i j, e j ≠d.target i)
    (hcd : ∀ i j, c.source i ≠d.source j) (i : Fin m) (j : Fin k) :
    (c.transport b e hcs hecs hect).source i ≠
      (d.transport b e hds heds hedt).source j := by
  intro h
  have hh := congrArg Subtype.val (Sum.inl.inj h)
  exact hcd i j (Sum.inl.inj hh)

end GridHardness.XorLineSchedule.Bundle
