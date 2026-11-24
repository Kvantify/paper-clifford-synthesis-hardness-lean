/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryIntervals
public import GridHardness.XorLineRegistryRetire

/-!
# XOR Line Registry Interval Selection

Effective selection of the actual residual bundle at a prescribed crossing.
The lookup uses a finite enumeration and the numerical interval labels.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry

namespace Intervals
variable {B : Type*}

/-- A cut affects only its own line and its own height. -/
theorem coverage_cut_separate [DecidableEq B] (segments : B → Interval) (b : B)
    (height : Nat) (hcut : (segments b).lower <height ∧ height <(segments b).upper)
    (line z : Nat) (hsep : line ≠(segments b).line ∨ z ≠height) :
    (∃ c, (cut segments b height c).Contains line z) ↔
      ∃ c, (segments c).Contains line z := by
  rcases hsep with hl | hz
  · constructor
    · rintro ⟨c,hc⟩
      exact ⟨parent b c,contains_parent segments b height hcut c line z hc⟩
    · rintro ⟨c,hc⟩
      have hcb : c≠b := by
        intro he; subst c; exact hl hc.1.symm
      exact ⟨.inl ⟨c,hcb⟩,hc⟩
  · exact coverage_cut segments b height hcut line z hz

def extend (segments : B → Interval) (line upper : Nat) : Option B → Interval
  | none => ⟨line,0,upper⟩
  | some b => segments b

theorem unique_extend (segments : B → Interval) (line upper : Nat)
    (hu : Unique segments) (hfresh : ∀ b, (segments b).line ≠line) :
    Unique (extend segments line upper) := by
  intro i z b c hb hc
  cases b with
  | none =>
    cases c with
    | none => rfl
    | some c => exact False.elim (hfresh c (hc.1.trans hb.1.symm))
  | some b =>
    cases c with
    | none => exact False.elim (hfresh b (hb.1.trans hc.1.symm))
    | some c => exact congrArg some (hu i z b c hb hc)

theorem coverage_extend (segments : B → Interval) (line upper i z : Nat) :
    (∃b, (extend segments line upper b).Contains i z) ↔
      (i=line ∧ 0<z ∧ z<upper) ∨ ∃b, (segments b).Contains i z := by
  constructor
  · rintro ⟨b,hb⟩
    cases b with
    | none => exact Or.inl ⟨hb.1.symm,hb.2⟩
    | some b => exact Or.inr ⟨b,hb⟩
  · rintro (⟨rfl,hz⟩ | ⟨b,hb⟩)
    · exact ⟨none,rfl,hz⟩
    · exact ⟨some b,hb⟩

/-- Explicit enumeration after replacing one segment by its two continuations. -/
def splitEnum [DecidableEq B] (enum : List B) (b : B) : List (Registry.SplitIndex b) :=
  (enum.attach.filterMap fun c => if h : c.val=b then none else some (.inl ⟨c.val,h⟩)) ++
    [.inr true,.inr false]

theorem splitEnum_complete [DecidableEq B] (enum : List B) (b : B)
    (hc : ∀ c, c ∈enum) : ∀c, c∈splitEnum enum b := by
  intro c
  cases c with
  | inl c =>
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    refine ⟨⟨c.val,hc c.val⟩,List.mem_attach _ _,?_⟩
    simp only [dite_eq_right c.property]
  | inr s => cases s <;> simp [splitEnum]

theorem splitEnum_length_le [DecidableEq B] (enum : List B) (b : B) :
    (splitEnum enum b).length≤enum.length+2 := by
  have h := List.length_filterMap_le
    (f := fun c : {c // c∈enum} => if h : c.val=b then none else
      some (Sum.inl ⟨c.val,h⟩ : Registry.SplitIndex b)) (l := enum.attach)
  simpa only [splitEnum,List.length_append,List.length_cons,List.length_nil,
    List.length_attach] using Nat.add_le_add_right h 2

/-- The finite search is an ordinary list operation, with no choice of a
Hamiltonian traversal or promised port behaviour. -/
def lookup (segments : B → Interval) (enum : List B) (line height : Nat) : Option B :=
  enum.find? (fun b => decide ((segments b).Contains line height))

theorem lookup_sound (segments : B → Interval) (enum : List B) (line height : Nat)
    {b : B} (hb : lookup segments enum line height =some b) :
    (segments b).Contains line height := by
  have h := List.find?_some (p := fun c => decide ((segments c).Contains line height)) hb
  exact of_decide_eq_true h

theorem lookup_exists (segments : B → Interval) (enum : List B) (line height : Nat)
    (henum : ∀ b, b ∈enum) (hc : ∃ b, (segments b).Contains line height) :
    ∃b, lookup segments enum line height=some b := by
  cases h : lookup segments enum line height with
  | none =>
    obtain ⟨b,hb⟩ := hc
    have hn := List.find?_eq_none.mp h b (henum b)
    exact False.elim (hn (decide_eq_true hb))
  | some b => exact ⟨b,rfl⟩

theorem lookup_unique (segments : B → Interval) (enum : List B) (line height : Nat)
    (hu : Unique segments) {b : B} (hb : lookup segments enum line height =some b) :
    ∀c, (segments c).Contains line height → c=b :=
  fun c hc => hu line height c b hc (lookup_sound segments enum line height hb)

end Intervals

namespace Positioned
variable {V B : Type*} {D : V → V → Prop} {n : Nat}

/-- Once an inserted XOR has crossed all old lines, its remaining section
becomes the bundle for the new line. -/
def retire (r : Positioned D (Fin (n +1)) B) (line upper : Nat)
    (hfresh : ∀ b, (r.segments b).line ≠line) : Positioned D (Fin n) (Option B) where
  registry := r.registry.retire
  segments := Intervals.extend r.segments line upper
  unique := Intervals.unique_extend r.segments line upper r.unique hfresh

end Positioned
end GridHardness.XorLineRegistry
