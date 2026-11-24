/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineDegree
public import GridHardness.XorLineDegreeSubdivision

/-!
# XOR Line Degree Bundle

Actual bundle refinement preserves the directed subcubic bounds. External
row ports have unique neighbors by subdivision; XOR ports have at most one
external neighbor because they already have an internal neighbor.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule.Bundle
open XorLine
open XorWire.NetworkDegree (inDegree outDegree)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

variable {V : Type*} {D : V → V → Prop} {n : Nat}

theorem outside_old (e : Fin 8 → V) (o : Marked.Outside (sourceMarker (n := n) e)) :
    ∃ v : V, o.val = Sum.inl v := by
  cases h : o.val with
  | inl v => exact ⟨v, rfl⟩
  | inr p => exact False.elim (o.property ⟨.inr p, h.symm⟩)

noncomputable def outsideOriginal (e : Fin 8 → V)
    (o : Marked.Outside (sourceMarker (n := n) e)) : V := (outside_old e o).choose

theorem outside_val (e : Fin 8 → V) (o : Marked.Outside (sourceMarker (n := n) e)) :
    o.val = Sum.inl (outsideOriginal e o) := (outside_old e o).choose_spec

theorem outsideOriginal_injective (e : Fin 8 → V) :
    Function.Injective (outsideOriginal (n := n) e) := by
  intro a b he
  apply Subtype.ext
  rw [outside_val e a, outside_val e b, he]

theorem outsideOriginal_ne_xor (e : Fin 8 → V)
    (o : Marked.Outside (sourceMarker (n := n) e)) (j : Fin 8) :
    outsideOriginal e o ≠ e j := by
  intro he
  apply o.property
  exact ⟨.inl j, (congrArg Sum.inl he.symm).trans (outside_val e o).symm⟩

private theorem unique_external {A B : Type*} [Fintype A]
    (P : A → Prop) (Q : B → Prop) (f : B → A) (hf : Function.Injective f)
    (z : A) (hz : P z) (hn : ∀ b, Q b → f b ≠ z) (he : ∀ b, Q b → P (f b))
    (hb : by classical exact (Finset.univ.filter P).card ≤ 2) :
    ∀ a b, Q a → Q b → a = b := by
  classical
  intro a b ha hc
  by_contra hab
  have hfab : f a ≠ f b := fun h => hab (hf h)
  have hza : z ≠ f a := (hn a ha).symm
  have hzb : z ≠ f b := (hn b hc).symm
  have hs : ({z, f a, f b} : Finset A) ⊆ Finset.univ.filter P := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he a ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he b hc⟩
  have hk := Finset.card_le_card hs
  have hh : ({z, f a, f b} : Finset A).card = 3 := by simp [hza, hzb, hfab]
  omega

variable (b : Bundle D n) (e : Fin 8 → V)

theorem enter_unique [Fintype V] (hx : XorIsolation D e)
    (hin : ∀ v, inDegree D v ≤ 2) (p : Port n)
    (a c : Marked.Outside (sourceMarker (n := n) e))
    (ha : Marked.enter (Subdivision.Adj D b.source b.target) (sourceMarker e) a p)
    (hc : Marked.enter (Subdivision.Adj D b.source b.target) (sourceMarker e) c p) : a = c := by
  cases p with
  | inr i =>
    apply outsideOriginal_injective e
    change Subdivision.Adj D b.source b.target a.val (.inr (i, false)) at ha
    change Subdivision.Adj D b.source b.target c.val (.inr (i, false)) at hc
    rw [outside_val e a] at ha
    rw [outside_val e c] at hc
    exact ha.1.trans hc.1.symm
  | inl choice =>
    let j : Fin 8 := if choice then 3 else 4
    let k : Fin 8 := if choice then 2 else 5
    have hedge : D (e k) (e j) := (hx.internal k j).mpr (by cases choice <;> decide)
    apply unique_external (fun v => D v (e j))
      (fun o => Marked.enter (Subdivision.Adj D b.source b.target) (sourceMarker e) o (.inl choice))
      (outsideOriginal e) (outsideOriginal_injective e) (e k) hedge
      (fun o _ => outsideOriginal_ne_xor e o k) ?_ (hin (e j)) a c ha hc
    intro o ho
    change Subdivision.Adj D b.source b.target o.val (.inl (e j)) at ho
    rw [outside_val e o] at ho
    exact ho.1

theorem leave_unique [Fintype V] (hx : XorIsolation D e)
    (hout : ∀ v, outDegree D v ≤ 2) (p : Port n)
    (a c : Marked.Outside (sourceMarker (n := n) e))
    (ha : Marked.leave (Subdivision.Adj D b.source b.target) (sourceMarker e) p a)
    (hc : Marked.leave (Subdivision.Adj D b.source b.target) (sourceMarker e) p c) : a = c := by
  cases p with
  | inr i =>
    apply outsideOriginal_injective e
    change Subdivision.Adj D b.source b.target (.inr (i, true)) a.val at ha
    change Subdivision.Adj D b.source b.target (.inr (i, true)) c.val at hc
    rw [outside_val e a] at ha
    rw [outside_val e c] at hc
    exact ha.2.trans hc.2.symm
  | inl choice =>
    let j : Fin 8 := if choice then 0 else 7
    let k : Fin 8 := if choice then 1 else 6
    have hedge : D (e j) (e k) := (hx.internal j k).mpr (by cases choice <;> decide)
    apply unique_external (fun v => D (e j) v)
      (fun o => Marked.leave (Subdivision.Adj D b.source b.target) (sourceMarker e) (.inl choice) o)
      (outsideOriginal e) (outsideOriginal_injective e) (e k) hedge
      (fun o _ => outsideOriginal_ne_xor e o k) ?_ (hout (e j)) a c ha hc
    intro o ho
    change Subdivision.Adj D b.source b.target (.inl (e j)) o.val at ho
    rw [outside_val e o] at ho
    exact ho.1

/-- The four-row crossing is subcubic whenever the actual source
graph is subcubic, with in/out degree at most two. -/
theorem refined_degree_bounds [Fintype V] (b : Bundle D 4) (e : Fin 8 → V)
    (he : Function.Injective e) (hx : XorIsolation D e)
    (hs : ∀ i j, e j ≠ b.source i) (ht : ∀ i j, e j ≠ b.target i)
    (hin : ∀ v, inDegree D v ≤ 2) (hout : ∀ v, outDegree D v ≤ 2)
    (htotal : ∀ v, inDegree D v + outDegree D v ≤ 3) (v : b.RefinedVertex e) :
    inDegree (b.refined e) v ≤ 2 ∧ outDegree (b.refined e) v ≤ 2 ∧
      inDegree (b.refined e) v + outDegree (b.refined e) v ≤ 3 := by
  cases v with
  | inr w =>
    exact XorLine.Degree.cell_degree_bounds
      (Marked.outside (Subdivision.Adj D b.source b.target) (sourceMarker e))
      (Marked.enter (Subdivision.Adj D b.source b.target) (sourceMarker e))
      (Marked.leave (Subdivision.Adj D b.source b.target) (sourceMarker e))
      (b.enter_unique e hx hin) (b.leave_unique e hx hout) w
  | inl o =>
    have h := sourceMarker_isolated D e hx b.source b.target hs ht
    change inDegree (Marked.replacement _ _) (.inl o) ≤ 2 ∧
      outDegree (Marked.replacement _ _) (.inl o) ≤ 2 ∧
      inDegree (Marked.replacement _ _) (.inl o) + outDegree (Marked.replacement _ _) (.inl o) ≤ 3
    rw [XorLine.Degree.outside_inDegree_eq _ _ (sourceMarker_injective e he) h,
      XorLine.Degree.outside_outDegree_eq _ _ (sourceMarker_injective e he) h,
      outside_val e o]
    have hi := Subdivision.Degree.old_in_le D b.source b.target b.source_injective b.edge
      (outsideOriginal e o)
    have ho := Subdivision.Degree.old_out_le D b.source b.target b.target_injective b.edge
      (outsideOriginal e o)
    have h1 := hin (outsideOriginal e o)
    have h2 := hout (outsideOriginal e o)
    have h3 := htotal (outsideOriginal e o)
    omega

end GridHardness.XorLineSchedule.Bundle
