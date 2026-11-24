/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingVerticalCode

/-!
# SAT Crossing Extrema Code

Bounded-list programs select the first and last crossing in each wire
group. Empty groups remain empty. The programs compare explicit cell labels,
never iterate up to a coordinate magnitude.
-/

@[expose] public section

namespace GridHardness.SatCrossingExtremaCode
open CliffordComplexity SatCrossingCode SatCrossingConnectionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- A competing cell is farther right (`last = true`) or farther left. -/
def competitor (last : Bool) : Code ConnectionTy .bool :=
  if last then forward else .comp (.pair .snd .fst) forward

theorem competitor_eval (last : Bool) (a b : Nat × Nat) :
    (competitor last).eval (a,b)=true ↔
      a.2=b.2 ∧ if last then a.1<b.1 else b.1<a.1 := by
  cases last
  · change forward.eval (b,a)=true ↔ _
    rw [forward_eval]
    simp only [Bool.false_eq_true, ite_false]
    tauto
  · exact forward_eval a b

def extremeTest (last : Bool) : Code (.pair PairListTy PairTy) .bool :=
  Code.isNil (.comp (.pair .snd .fst) (Code.filterEnv (competitor last)))

theorem extremeTest_eval (last : Bool) (l : List (Nat × Nat)) (a : Nat × Nat) :
    (extremeTest last).eval (l,a)=true ↔
      ∀ b∈l, a.2=b.2 → if last then b.1≤a.1 else a.1≤b.1 := by
  rw [extremeTest, isNil_eval_true]
  change (Code.filterEnv (competitor last)).eval (a,l)=[] ↔ _
  rw [filterEnv_eval, List.filter_eq_nil_iff]
  constructor
  · intro h b hb he
    have hn := h b hb
    by_contra hle
    apply hn
    apply (competitor_eval last a b).mpr
    refine ⟨he,?_⟩
    cases last <;> dsimp at hle ⊢ <;> omega
  · intro h b hb ht
    obtain ⟨he,hlt⟩ := (competitor_eval last a b).mp ht
    have hle := h b hb he
    cases last <;> dsimp at hlt hle <;> omega

def extrema (last : Bool) : Code PairListTy PairListTy :=
  .comp (.pair .id .id) (Code.filterEnv (extremeTest last))

theorem extrema_eval (last : Bool) (l : List (Nat × Nat)) :
    (extrema last).eval l = l.filter (fun a => (extremeTest last).eval (l,a)) :=
  filterEnv_eval _ _ _

theorem mem_extrema (last : Bool) (l : List (Nat × Nat)) (a : Nat × Nat) :
    a∈(extrema last).eval l ↔
      a∈l ∧ ∀ b∈l, a.2=b.2 → if last then b.1≤a.1 else a.1≤b.1 := by
  rw [extrema_eval, List.mem_filter, extremeTest_eval]

theorem extrema_unique (last : Bool) (l : List (Nat × Nat)) (a b : Nat × Nat)
    (ha : a ∈(extrema last).eval l) (hb : b ∈(extrema last).eval l) (he : a.2 =b.2) : a=b := by
  obtain ⟨hal,ha⟩ := (mem_extrema last l a).mp ha
  obtain ⟨hbl,hb⟩ := (mem_extrema last l b).mp hb
  have hab := ha b hbl he
  have hba := hb a hal he.symm
  apply Prod.ext _ he
  cases last <;> dsimp at hab hba <;> omega

theorem extrema_nodup (last : Bool) (l : List (Nat × Nat)) (hl : l.Nodup) :
    ((extrema last).eval l).Nodup := by
  rw [extrema_eval]
  exact hl.filter _

/-- At most one selected cell per group, so the output is linear in the
number of wire groups, even when the input contains quadratically many cells. -/
theorem extrema_length_le (last : Bool) (l : List (Nat × Nat)) (hl : l.Nodup)
    (N : Nat) (hb : ∀ a ∈l, a.2 <N) : ((extrema last).eval l).length≤N := by
  have hn : (((extrema last).eval l).map Prod.snd).Nodup := by
    apply List.Nodup.map_on _ (extrema_nodup last l hl)
    intro a ha b hb he
    exact extrema_unique last l a b ha hb he
  have hs : ((extrema last).eval l).map Prod.snd ⊆ List.range N := by
    intro b h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    exact List.mem_range.mpr (hb a ((mem_extrema last l a).mp ha).1)
  simpa only [List.length_map, List.length_range] using hn.length_le_of_subset hs

def sameGroup : Code (.pair .nat PairTy) .bool :=
  .comp (.pair .fst (.comp .snd .snd)) .natEq

theorem sameGroup_eval (group : Nat) (a : Nat × Nat) :
    sameGroup.eval (group,a)=true ↔ group=a.2 := by
  change decide (group=a.2)=true ↔ _
  simp only [decide_eq_true_eq]

def atGroup (last : Bool) : Code (.pair PairListTy .nat) PairListTy :=
  .comp (.pair .snd (.comp .fst (extrema last))) (Code.filterEnv sameGroup)

theorem mem_atGroup (last : Bool) (l : List (Nat × Nat)) (group : Nat) (a : Nat × Nat) :
    a∈(atGroup last).eval (l,group) ↔ a∈(extrema last).eval l ∧ group=a.2 := by
  change a∈(Code.filterEnv sameGroup).eval (group,(extrema last).eval l) ↔ _
  rw [filterEnv_eval, List.mem_filter, sameGroup_eval]

theorem atGroup_length_le_one (last : Bool) (l : List (Nat × Nat)) (hl : l.Nodup)
    (group : Nat) : ((atGroup last).eval (l,group)).length≤1 := by
  have hn : ((atGroup last).eval (l,group)).Nodup := by
    change ((Code.filterEnv sameGroup).eval (group,(extrema last).eval l)).Nodup
    rw [filterEnv_eval]
    exact (extrema_nodup last l hl).filter _
  have he : ∀ a∈(atGroup last).eval (l,group), ∀ b∈(atGroup last).eval (l,group), a=b := by
    intro a ha b hb
    have ha' := (mem_atGroup last l group a).mp ha
    have hb' := (mem_atGroup last l group b).mp hb
    exact extrema_unique last l a b ha'.1 hb'.1 (ha'.2.symm.trans hb'.2)
  cases h : (atGroup last).eval (l,group) with
  | nil => simp
  | cons a as =>
    have has : as=[] := by
      by_contra hne
      obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil as hne
      have hab := he a (by rw [h]; simp) b (by rw [h]; exact List.mem_cons_of_mem a hb)
      rw [h] at hn
      exact (List.nodup_cons.mp hn).1 (hab ▸ hb)
    simp [has]

private def positions (l : List (Nat × Nat)) (group : Nat) : Finset Nat :=
  ((l.filter (fun a => decide (a.2=group))).map Prod.fst).toFinset

private theorem mem_positions (l : List (Nat × Nat)) (group k : Nat) :
    k∈positions l group ↔ (k,group)∈l := by
  simp only [positions, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,b⟩,⟨hab,hb⟩,ha⟩
    dsimp at hb ha
    subst a
    subst b
    exact hab
  · intro h
    exact ⟨(k,group),⟨h,rfl⟩,rfl⟩

theorem atGroup_nonempty_iff (last : Bool) (l : List (Nat × Nat)) (group : Nat) :
    (∃ a, a∈(atGroup last).eval (l,group)) ↔ ∃ a∈l, a.2=group := by
  constructor
  · rintro ⟨a,ha⟩
    have h := (mem_atGroup last l group a).mp ha
    exact ⟨a,((mem_extrema last l a).mp h.1).1,h.2.symm⟩
  · rintro ⟨a,ha,hag⟩
    have hn : (positions l group).Nonempty := by
      refine ⟨a.1,(mem_positions l group a.1).mpr ?_⟩
      simpa only [← hag] using ha
    have hex : ∃ k∈positions l group, ∀ b∈positions l group,
        if last then b≤k else k≤b := by
      cases last
      · exact ⟨_,Finset.min'_mem _ hn,fun b hb => Finset.min'_le _ b hb⟩
      · exact ⟨_,Finset.max'_mem _ hn,fun b hb => Finset.le_max' _ b hb⟩
    obtain ⟨k,hk,hbound⟩ := hex
    refine ⟨(k,group),(mem_atGroup last l group (k,group)).mpr ⟨?_,rfl⟩⟩
    apply (mem_extrema last l (k,group)).mpr
    refine ⟨(mem_positions l group k).mp hk,?_⟩
    intro b hb hbg
    apply hbound b.1
    apply (mem_positions l group b.1).mpr
    change group=b.2 at hbg
    rw [hbg]
    exact hb

/-- Absence of an extreme is exactly absence of crossings in that group;
there is no default cell that might be mistaken for a real crossing. -/
theorem atGroup_nil_iff (last : Bool) (l : List (Nat × Nat)) (group : Nat) :
    (atGroup last).eval (l,group)=[] ↔ ∀ a∈l, a.2≠group := by
  have h := atGroup_nonempty_iff last l group
  rw [← not_iff_not] at h
  simpa only [not_exists, not_and, List.eq_nil_iff_forall_not_mem] using h

theorem atGroup_length_one_iff (last : Bool) (l : List (Nat × Nat)) (hl : l.Nodup)
    (group : Nat) : ((atGroup last).eval (l,group)).length=1 ↔ ∃ a∈l, a.2=group := by
  have hb := atGroup_length_le_one last l hl group
  have hn := atGroup_nil_iff last l group
  rw [← not_iff_not] at hn
  simp only [not_forall, not_not, exists_prop, ← List.length_eq_zero_iff] at hn
  constructor
  · intro h
    exact hn.mp (by omega)
  · intro h
    have h := hn.mpr h
    omega

end GridHardness.SatCrossingExtremaCode
