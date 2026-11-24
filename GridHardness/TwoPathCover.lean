/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GadgetReplacement
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.Chain

/-!
# Two Path Cover

Enumerate two paths that together cover the vertices of the routing graph.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PathCover

namespace TwoLists

def size {W : Type*} (routes : Bool → List W) (b : Bool) : Nat := (routes b).length - 1

theorem length_eq {W : Type*} (routes : Bool → List W)
    (hn : ∀ b, routes b ≠ []) (b : Bool) : (routes b).length = size routes b + 1 := by
  have hh : (routes b).length ≠ 0 := fun h => hn b (List.eq_nil_of_length_eq_zero h)
  unfold size
  omega

def point {W : Type*} (routes : Bool → List W) (hn : ∀ b, routes b ≠ []) :
    Blocks (size routes) → W := fun ⟨b, i⟩ =>
  (routes b).get (Fin.cast (length_eq routes hn b).symm i)

theorem point_bijective {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1) :
    Function.Bijective (point routes hn) := by
  have hnd : (routes false ++ routes true).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    simpa only [List.count_append, hc w] using (show 1 ≤ 1 from le_rfl)
  have hmem (b : Bool) (i : Fin (size routes b + 1)) :
      point routes hn ⟨b, i⟩ ∈ routes b := List.get_mem _ _
  constructor
  · rintro ⟨b, i⟩ ⟨c, j⟩ he
    have hb : b = c := by
      cases b <;> cases c
      · rfl
      · have hp := hnd.disjoint (hmem false i)
        exact False.elim (hp (he ▸ hmem true j))
      · have hp := hnd.disjoint (hmem false j)
        exact False.elim (hp (he.symm ▸ hmem true i))
      · rfl
    subst c
    have hd : (routes b).Nodup := by
      cases b
      · exact hnd.of_append_left
      · exact hnd.of_append_right
    have hij := hd.get_inj_iff.mp he
    have hv : i.val = j.val := congrArg (fun k : Fin (routes b).length => k.val) hij
    exact congrArg (fun k : Fin (size routes b + 1) =>
      (⟨b, k⟩ : Blocks (size routes))) (Fin.ext hv)
  · intro w
    have hm : w ∈ routes false ++ routes true := by
      apply List.count_pos_iff.mp
      simpa only [List.count_append, hc w] using (show 0 < 1 from Nat.zero_lt_one)
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
      exact ⟨⟨false, Fin.cast (length_eq routes hn false) i⟩, hi⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
      exact ⟨⟨true, Fin.cast (length_eq routes hn true) i⟩, hi⟩

noncomputable def cover {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1) : Cover Bool W where
  size := size routes
  equiv := Equiv.ofBijective (point routes hn) (point_bijective routes hn hc)

@[simp] theorem cover_apply {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1)
    (b : Bool) (i : Fin (size routes b + 1)) :
    (cover routes hn hc).equiv ⟨b, i⟩ =
      (routes b).get (Fin.cast (length_eq routes hn b).symm i) := rfl

theorem internalEdges {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1)
    (D : W → W → Prop) (hchain : ∀ b, (routes b).IsChain D) :
    (cover routes hn hc).InternalEdges D := by
  intro b i
  change Fin (size routes b) at i
  have hlen := length_eq routes hn b
  have hj : i.val + 1 < (routes b).length := by omega
  exact (List.isChain_iff_getElem.mp (hchain b)) i.val hj

theorem followedBy {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1)
    (step : Equiv.Perm W)
    (hchain : ∀ b, (routes b).IsChain (fun u v => step u = v)) :
    (cover routes hn hc).FollowedBy step := by
  intro b i
  apply (cover routes hn hc).equiv.injective
  simp only [Cover.conjugate, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact internalEdges routes hn hc (fun u v => step u = v) hchain b i

@[simp] theorem first_eq {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1) (b : Bool) :
    (cover routes hn hc).first b = (routes b).head (hn b) := by
  rw [List.head_eq_getElem]
  rfl

@[simp] theorem finish_eq {W : Type*} [DecidableEq W]
    (routes : Bool → List W) (hn : ∀ b, routes b ≠ [])
    (hc : ∀ w, (routes false).count w + (routes true).count w = 1) (b : Bool) :
    (cover routes hn hc).finish b = (routes b).getLast (hn b) := by
  rw [List.getLast_eq_getElem]
  rfl

end TwoLists

namespace Cover

/-- Add each outside vertex as a singleton path. Only the replaced gadget's
vertices are partitioned into longer paths. -/
def extend {I W : Type*} (c : Cover I W) (O : Type*) : Cover (O ⊕ I) (O ⊕ W) where
  size := Sum.elim (fun _ => 0) c.size
  equiv :=
    { toFun := fun w => match w with
        | ⟨Sum.inl o, _⟩ => Sum.inl o
        | ⟨Sum.inr i, j⟩ => Sum.inr (c.equiv ⟨i, j⟩)
      invFun := fun w => match w with
        | Sum.inl o => ⟨Sum.inl o, 0⟩
        | Sum.inr w => ⟨Sum.inr (c.equiv.symm w).1, (c.equiv.symm w).2⟩
      left_inv := by
        rintro ⟨o | i, j⟩
        · change Fin 1 at j
          have hj : j = 0 := Subsingleton.elim _ _
          cases hj
          rfl
        · exact congrArg (fun v : Blocks c.size =>
            (⟨Sum.inr v.1, v.2⟩ : Blocks (Sum.elim (fun _ : O => 0) c.size)))
              (c.equiv.symm_apply_apply ⟨i, j⟩)
      right_inv := by
        rintro (o | w)
        · rfl
        · simp }

@[simp] theorem extend_apply_left {I W O : Type*} (c : Cover I W) (o : O)
    (j : Fin 1) : (c.extend O).equiv ⟨Sum.inl o, j⟩ = Sum.inl o := rfl

@[simp] theorem extend_apply_right {I W O : Type*} (c : Cover I W) (i : I)
    (j : Fin (c.size i + 1)) :
    (c.extend O).equiv ⟨Sum.inr i, j⟩ = Sum.inr (c.equiv ⟨i, j⟩) := rfl

@[simp] theorem extend_first_left {I W O : Type*} (c : Cover I W) (o : O) :
    (c.extend O).first (Sum.inl o) = Sum.inl o := rfl

@[simp] theorem extend_first_right {I W O : Type*} (c : Cover I W) (i : I) :
    (c.extend O).first (Sum.inr i) = Sum.inr (c.first i) := rfl

@[simp] theorem extend_finish_left {I W O : Type*} (c : Cover I W) (o : O) :
    (c.extend O).finish (Sum.inl o) = Sum.inl o := rfl

@[simp] theorem extend_finish_right {I W O : Type*} (c : Cover I W) (i : I) :
    (c.extend O).finish (Sum.inr i) = Sum.inr (c.finish i) := rfl

theorem extend_internalEdges {I W O : Type*} (c : Cover I W)
    (D : (O ⊕ W) → (O ⊕ W) → Prop)
    (hi : ∀ (i : I) (j : Fin (c.size i)),
      D (Sum.inr (c.equiv ⟨i, j.castSucc⟩)) (Sum.inr (c.equiv ⟨i, j.succ⟩))) :
    (c.extend O).InternalEdges D := by
  rintro (o | i) j
  · exact Fin.elim0 j
  · exact hi i j

theorem extend_followedBy {I W O : Type*} (c : Cover I W) (step : Equiv.Perm (O ⊕ W))
    (hi : ∀ (i : I) (j : Fin (c.size i)),
      step (Sum.inr (c.equiv ⟨i, j.castSucc⟩)) = Sum.inr (c.equiv ⟨i, j.succ⟩)) :
    (c.extend O).FollowedBy step := by
  intro i j
  apply (c.extend O).equiv.injective
  simp only [conjugate, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact extend_internalEdges c (fun u v => step u = v) hi i j

end Cover
end GridHardness.PathCover
