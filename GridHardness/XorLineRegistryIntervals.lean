/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistrySplit

/-!
# XOR Line Registry Intervals

Interval labels for the two actual residual bundles of a crossed line.
This gives a proved selection invariant for every subsequent distinct crossing
height; it asserts no ambient planar drawing.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry

structure Interval where
  line : Nat
  lower : Nat
  upper : Nat
  deriving DecidableEq

def Interval.Contains (s : Interval) (line height : Nat) : Prop :=
  s.line=line ∧ s.lower<height ∧ height<s.upper

instance (s : Interval) (line height : Nat) : Decidable (s.Contains line height) := by
  unfold Interval.Contains
  infer_instance

namespace Intervals
variable {B : Type*}

def parent (b : B) : Registry.SplitIndex b → B
  | .inl c => c.val
  | .inr _ => b

/-- `true` is the lower continuation, towards the original true ports. -/
def cut (segments : B → Interval) (b : B) (height : Nat) : Registry.SplitIndex b → Interval
  | .inl c => segments c.val
  | .inr true => ⟨(segments b).line,(segments b).lower,height⟩
  | .inr false => ⟨(segments b).line,height,(segments b).upper⟩

def Unique (segments : B → Interval) : Prop :=
  ∀ line height c d, (segments c).Contains line height →
    (segments d).Contains line height → c=d

theorem contains_parent (segments : B → Interval) (b : B) (height : Nat)
    (hcut : (segments b).lower <height ∧ height <(segments b).upper)
    (c : Registry.SplitIndex b) (line z : Nat)
    (hc : (cut segments b height c).Contains line z) :
    (segments (parent b c)).Contains line z := by
  cases c with
  | inl c => exact hc
  | inr s =>
    cases s <;> simp only [cut,parent,Interval.Contains] at hc ⊢ <;>
      exact ⟨hc.1,by omega,by omega⟩

theorem unique_cut (segments : B → Interval) (b : B) (height : Nat)
    (hcut : (segments b).lower <height ∧ height <(segments b).upper)
    (hu : Unique segments) : Unique (cut segments b height) := by
  intro line z c d hc hd
  have hp := hu line z (parent b c) (parent b d)
    (contains_parent segments b height hcut c line z hc)
    (contains_parent segments b height hcut d line z hd)
  cases c with
  | inl c =>
    cases d with
    | inl d => exact congrArg Sum.inl (Subtype.ext hp)
    | inr t => exact False.elim (c.property hp)
  | inr s =>
    cases d with
    | inl d => exact False.elim (d.property hp.symm)
    | inr t =>
      cases s <;> cases t
      · rfl
      · simp only [cut,Interval.Contains] at hc hd; omega
      · simp only [cut,Interval.Contains] at hc hd; omega
      · rfl

/-- Cutting at one height preserves coverage at every other height. -/
theorem coverage_cut [DecidableEq B] (segments : B → Interval) (b : B) (height : Nat)
    (hcut : (segments b).lower <height ∧ height <(segments b).upper)
    (line z : Nat) (hz : z ≠height) :
    (∃ c, (cut segments b height c).Contains line z) ↔
      ∃ c, (segments c).Contains line z := by
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨parent b c,contains_parent segments b height hcut c line z hc⟩
  · rintro ⟨c,hc⟩
    by_cases hcb : c=b
    · subst c
      by_cases hzh : z<height
      · exact ⟨.inr true,hc.1,hc.2.1,hzh⟩
      · exact ⟨.inr false,hc.1,by change height<z; omega,hc.2.2⟩
    · exact ⟨.inl ⟨c,hcb⟩,hc⟩

/-- The next crossing has a unique concrete registered bundle. -/
theorem existsUnique_after [DecidableEq B] (segments : B → Interval) (b : B) (height : Nat)
    (hcut : (segments b).lower <height ∧ height <(segments b).upper)
    (hu : Unique segments) (line z : Nat) (hz : z ≠height)
    (hc : ∃ c, (segments c).Contains line z) :
    ∃! c, (cut segments b height c).Contains line z := by
  obtain ⟨c,hc⟩ := (coverage_cut segments b height hcut line z hz).mpr hc
  exact ⟨c,hc,fun d hd => unique_cut segments b height hcut hu line z d c hd hc⟩

end Intervals

/-- Numerical labels attached to the actual edge registry. Uniqueness is a
coordinate interval property, independent of Hamiltonian traversals. -/
structure Positioned {V : Type*} (D : V → V → Prop) (X B : Type*) where
  registry : Registry D X B
  segments : B → Interval
  unique : Intervals.Unique segments

namespace Positioned
variable {V X B : Type*} {D : V → V → Prop} [DecidableEq X] [DecidableEq B]
variable (r : Positioned D X B)

/-- The actual graph replacement retains both sides, labelled by their split
intervals, with the per-arc direction choices already proved mandatory. -/
def cross (a : X) (b : B) (height : Nat)
    (hcut : (r.segments b).lower <height ∧ height <(r.segments b).upper) :
    Positioned (r.registry.crossAdj a b) X (Registry.SplitIndex b) where
  registry := r.registry.split a b BundleSegments.towardTrue
  segments := Intervals.cut r.segments b height
  unique := Intervals.unique_cut r.segments b height hcut r.unique

theorem cross_correct [Finite V] (a : X) (b : B) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (r.registry.crossAdj a b) :=
  r.registry.cross_correct a b

theorem crossing_available_after (a : X) (b : B) (height : Nat)
    (hcut : (r.segments b).lower <height ∧ height <(r.segments b).upper)
    (line z : Nat) (hz : z ≠height) (hc : ∃ c, (r.segments c).Contains line z) :
    ∃! c, ((r.cross a b height hcut).segments c).Contains line z :=
  Intervals.existsUnique_after r.segments b height hcut r.unique line z hz hc

end Positioned
end GridHardness.XorLineRegistry
