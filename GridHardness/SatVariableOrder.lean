/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatWireLayout
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# SAT Variable Order

Exact block positions in the variable-side occurrence order.

The prefix of a variable is the sum of the occurrence counts of all
earlier variables. Empty blocks are retained in this accounting, so no
assumption that every variable occurs is needed.
-/

@[expose] public section

namespace GridHardness.SatVariableOrder
open PlanarSatAssembly SatWireLayout
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

def count (φ : Formula n m) (v : Fin n) : Nat :=
  (occurrencesOf φ v).length

/-- Sum of occurrence counts in the first `i` variable blocks. -/
def offset (φ : Formula n m) (i : Nat) : Nat :=
  (((List.finRange n).take i).map (count φ)).sum

def «prefix» (φ : Formula n m) (v : Fin n) : Nat := offset φ v.val

def indexedOccurrence (φ : Formula n m) (v : Fin n) (k : Fin (count φ v)) :
    Occurrence m := (occurrencesOf φ v)[k.val]

@[simp] theorem indexedOccurrence_mem (φ : Formula n m) (v : Fin n)
    (k : Fin (count φ v)) : indexedOccurrence φ v k ∈ occurrencesOf φ v :=
  List.getElem_mem k.isLt

theorem indexedOccurrence_variable (φ : Formula n m) (v : Fin n)
    (k : Fin (count φ v)) :
    φ (indexedOccurrence φ v k).1 (indexedOccurrence φ v k).2 = v :=
  (mem_occurrencesOf φ v _).mp (indexedOccurrence_mem φ v k)

theorem mem_take_finRange (i : Nat) (v : Fin n) :
    v∈(List.finRange n).take i ↔ v.val < i := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j,hj,he⟩
    have hv := congrArg Fin.val he
    simp only [List.getElem_finRange,Fin.val_cast] at hv
    simp only [List.length_finRange] at hj
    omega
  · intro hv
    refine ⟨v.val,by simp; omega,?_⟩
    apply Fin.ext
    simp

theorem take_finRange_eq_filter (i : Nat) :
    (List.finRange n).take i =
      (List.finRange n).filter (fun v => decide (v.val < i)) := by
  rw [(List.nodup_finRange n).take_eq_filter_mem]
  apply List.filter_congr
  intro v _
  simp only [List.elem_eq_mem,mem_take_finRange]

/-- A prefix is literally the sum of counts of variables with smaller
indices, rather than a sum depending on which blocks are nonempty. -/
theorem prefix_sum_lower (φ : Formula n m) (v : Fin n) :
    «prefix» φ v =
      (((List.finRange n).filter (fun w => decide (w.val<v.val))).map (count φ)).sum := by
  simp only [«prefix»,offset,take_finRange_eq_filter]

theorem offset_eq_length (φ : Formula n m) (i : Nat) :
    offset φ i = (((List.finRange n).take i).flatMap (occurrencesOf φ)).length := by
  rw [List.length_flatMap]
  rfl

@[simp] theorem offset_zero (φ : Formula n m) : offset φ 0=0 := by
  simp [offset]

theorem sum_counts (φ : Formula n m) :
    ((List.finRange n).map (count φ)).sum=3*m := by
  have h := variableOrder_length φ
  rw [variableOrder,List.length_flatMap] at h
  exact h

@[simp] theorem offset_all (φ : Formula n m) : offset φ n=3*m := by
  unfold offset
  rw [List.take_of_length_le (by simp)]
  exact sum_counts φ

theorem offset_succ (φ : Formula n m) (v : Fin n) :
    offset φ (v.val+1)=«prefix» φ v+count φ v := by
  unfold offset «prefix»
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp [offset]

theorem offset_mono (φ : Formula n m) {i j : Nat} (hij : i ≤j) :
    offset φ i≤offset φ j := by
  rw [offset_eq_length,offset_eq_length]
  apply List.Sublist.length_le
  apply List.Sublist.flatMap
  have h := List.take_sublist i ((List.finRange n).take j)
  simpa only [List.take_take,Nat.min_eq_left hij] using h

theorem prefix_mono (φ : Formula n m) {v w : Fin n} (hvw : v ≤w) :
    «prefix» φ v≤«prefix» φ w := offset_mono φ hvw

/-- Earlier and later variable blocks have disjoint index intervals;
an unused variable simply contributes an interval of length zero. -/
theorem blocks_ordered (φ : Formula n m) {v w : Fin n} (hvw : v <w) :
    «prefix» φ v+count φ v≤«prefix» φ w := by
  rw [← offset_succ]
  exact offset_mono φ (by exact hvw)

theorem prefix_add_count_le (φ : Formula n m) (v : Fin n) :
    «prefix» φ v+count φ v≤3*m := by
  rw [← offset_succ,← offset_all φ]
  exact offset_mono φ (by omega)

theorem consecutive_prefix (φ : Formula n m) (v w : Fin n)
    (hvw : w.val =v.val +1) : «prefix» φ w=«prefix» φ v+count φ v := by
  change offset φ w.val=_
  rw [hvw,offset_succ]

/-- Split the actual variable order immediately before and after one
variable's complete occurrence list. -/
theorem variableOrder_split (φ : Formula n m) (v : Fin n) :
    variableOrder φ =
      ((List.finRange n).take v.val).flatMap (occurrencesOf φ) ++
      (occurrencesOf φ v ++
        ((List.finRange n).drop (v.val+1)).flatMap (occurrencesOf φ)) := by
  unfold variableOrder
  conv_lhs => rw [← List.take_append_drop v.val (List.finRange n)]
  rw [List.flatMap_append,List.drop_eq_getElem_cons (by simp)]
  simp

theorem indexedOccurrence_not_before (φ : Formula n m) (v : Fin n)
    (k : Fin (count φ v)) :
    indexedOccurrence φ v k ∉
      ((List.finRange n).take v.val).flatMap (occurrencesOf φ) := by
  intro h
  obtain ⟨w,hw,ho⟩ := List.mem_flatMap.mp h
  have hvar := (mem_occurrencesOf φ w _).mp ho
  rw [indexedOccurrence_variable φ v k] at hvar
  subst w
  have hv := (mem_take_finRange v.val v).mp hw
  omega

/-- The local index within a variable's block is translated by exactly
the prefix sum; this is the existing `SatWireLayout.variableRank`. -/
theorem variableRank_indexed (φ : Formula n m) (v : Fin n)
    (k : Fin (count φ v)) :
    (variableRank φ (indexedOccurrence φ v k)).val=«prefix» φ v+k.val := by
  let : BEq (Occurrence m) := instBEqOfDecidableEq
  rw [variableRank_val,variableOrder_split φ v,
    List.idxOf_append_of_notMem (indexedOccurrence_not_before φ v k),
    List.idxOf_append_of_mem (indexedOccurrence_mem φ v k)]
  have hk := (occurrencesOf_nodup φ v).idxOf_getElem k.val k.isLt
  change _+List.idxOf (indexedOccurrence φ v k) (occurrencesOf φ v)=_
  rw [show List.idxOf (indexedOccurrence φ v k) (occurrencesOf φ v)=k.val from hk]
  rw [← offset_eq_length]
  rfl

theorem indexedOccurrence_injective (φ : Formula n m) (v : Fin n) :
    Function.Injective (indexedOccurrence φ v) := by
  intro k l h
  have hr := congrArg (fun o => (variableRank φ o).val) h
  rw [variableRank_indexed,variableRank_indexed] at hr
  exact Fin.ext (by omega)

theorem exists_indexedOccurrence (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) (ho : o ∈occurrencesOf φ v) :
    ∃ k : Fin (count φ v), indexedOccurrence φ v k=o := by
  obtain ⟨k,hk,he⟩ := List.getElem_of_mem ho
  exact ⟨⟨k,hk⟩,he⟩

theorem consecutive_ranks (φ : Formula n m) (v : Fin n)
    (k l : Fin (count φ v)) (hkl : l.val =k.val +1) :
    (variableRank φ (indexedOccurrence φ v l)).val=
      (variableRank φ (indexedOccurrence φ v k)).val+1 := by
  rw [variableRank_indexed,variableRank_indexed,hkl]
  omega

theorem indexed_rank_bounds (φ : Formula n m) (v : Fin n)
    (k : Fin (count φ v)) :
    «prefix» φ v≤(variableRank φ (indexedOccurrence φ v k)).val ∧
      (variableRank φ (indexedOccurrence φ v k)).val<«prefix» φ v+count φ v := by
  rw [variableRank_indexed]
  omega

theorem rank_bounds (φ : Formula n m) (v : Fin n) (o : Occurrence m)
    (ho : φ o.1 o.2 =v) :
    «prefix» φ v≤(variableRank φ o).val ∧
      (variableRank φ o).val<«prefix» φ v+count φ v := by
  obtain ⟨k,rfl⟩ := exists_indexedOccurrence φ v o ((mem_occurrencesOf φ v o).mpr ho)
  exact indexed_rank_bounds φ v k

/-- A variable block contains exactly its own occurrences, as an
interval in the existing global wire numbering. -/
theorem rank_in_block_iff (φ : Formula n m) (v : Fin n) (o : Occurrence m) :
    («prefix» φ v≤(variableRank φ o).val ∧
      (variableRank φ o).val<«prefix» φ v+count φ v) ↔ φ o.1 o.2=v := by
  constructor
  · intro hv
    have ho := rank_bounds φ (φ o.1 o.2) o rfl
    rcases lt_trichotomy (φ o.1 o.2) v with h | h | h
    · have hb := blocks_ordered φ h
      omega
    · exact h
    · have hb := blocks_ordered φ h
      omega
  · exact rank_bounds φ v o

theorem first_rank (φ : Formula n m) (v : Fin n) (h : 0 <count φ v) :
    (variableRank φ (indexedOccurrence φ v ⟨0,h⟩)).val=«prefix» φ v := by
  rw [variableRank_indexed]
  exact Nat.add_zero _

theorem last_rank (φ : Formula n m) (v : Fin n) (h : 0 <count φ v) :
    (variableRank φ (indexedOccurrence φ v ⟨count φ v-1,by omega⟩)).val+1=
      «prefix» φ v+count φ v := by
  rw [variableRank_indexed]
  dsimp only
  omega

theorem earlier_block_rank_lt (φ : Formula n m) (v w : Fin n) (hvw : v <w)
    (k : Fin (count φ v)) (l : Fin (count φ w)) :
    variableRank φ (indexedOccurrence φ v k)<variableRank φ (indexedOccurrence φ w l) := by
  have h := blocks_ordered φ hvw
  have hk := indexed_rank_bounds φ v k
  have hl := indexed_rank_bounds φ w l
  exact show (variableRank φ (indexedOccurrence φ v k)).val<
    (variableRank φ (indexedOccurrence φ w l)).val from by omega

theorem count_eq_zero_iff (φ : Formula n m) (v : Fin n) :
    count φ v=0 ↔ ∀ o : Occurrence m, φ o.1 o.2≠v := by
  rw [count,List.length_eq_zero_iff]
  constructor
  · intro h o ho
    have hm := (mem_occurrencesOf φ v o).mpr ho
    simp [h] at hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro o ho
    exact h o ((mem_occurrencesOf φ v o).mp ho)

theorem unused_offset (φ : Formula n m) (v : Fin n) (h : count φ v =0) :
    offset φ (v.val+1)=«prefix» φ v := by
  simp only [offset_succ,h,Nat.add_zero]

end GridHardness.SatVariableOrder
