/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireLattice
public import GridHardness.SatCrossingRetirementSides

/-!
# SAT Clause Retirement Clearance

Clause links and the final retired-XOR routes. The first and last
crossings are selected from the actual request lists. Intersections with
retired side edges and residual lanes occur only at a common false-side
endpoint on a wire whose request list is empty. The final crossing links
are disjoint from the clause links.
-/

public section

namespace GridHardness.SatClauseRetirementClearance
open CliffordSynthesis PermutationWireLayout SatCrossingRouting
open SatCrossingRetirement SatCrossingRetirement.Segments
set_option autoImplicit false
abbrev Point := Int × Int

variable {N : Nat} (p : Equiv.Perm (Fin N))

theorem rowEnd_none_iff (j : Fin N) :
    Residual.rowEnd p j=none ↔ SatClauseWireLattice.firstRequest? p j=none :=
  (Catalogue.lastRequest_none p j).trans (SatClauseWireLattice.firstRequest_none p j).symm

/-- A clause link reaches the retired false column precisely when the
occurrence has no horizontal crossing. -/
theorem false_column_intersection (j : Fin N) (x : Int)
    (hx : x ≤SatClauseWireLattice.finishX p j)
    (hl : Placement.left (Residual.rowEnd p j) ≤x) :
    SatClauseWireLattice.firstRequest? p j=none ∧ x=0 := by
  cases hf : SatClauseWireLattice.firstRequest? p j with
  | none =>
    have he := (rowEnd_none_iff p j).mpr hf
    simp only [he,Placement.left] at hl
    simp only [SatClauseWireLattice.finishX,hf] at hx
    exact ⟨rfl,by omega⟩
  | some i =>
    have hi := SatClauseWireLattice.firstRequest_sound p i j hf
    cases he : Residual.rowEnd p j with
    | none =>
      exact False.elim ((SatClauseWireLattice.firstRequest_none p j).mp
        ((rowEnd_none_iff p j).mp he) i hi.1)
    | some k =>
      have hk := Catalogue.lastRequest_sound p k j he
      have hik := hi.2 k hk.1
      simp only [SatClauseWireLattice.finishX,hf] at hx
      simp only [he,Placement.left] at hl
      dsimp [low] at hx hl
      omega

/-- Every vertical lane reaching the height of a clause port lies
strictly beyond that clause link's first crossing. -/
theorem finish_lt_lane (i j : Fin N) (r : Fin 4) (hh : high p j ≤high p i) :
    SatClauseWireLattice.finishX p j<lane i r := by
  have hi := low_bounds i
  have hr := r.isLt
  cases hf : SatClauseWireLattice.firstRequest? p j with
  | none =>
    simp only [SatClauseWireLattice.finishX,hf]
    dsimp [lane]
    omega
  | some a =>
    have ha := SatClauseWireLattice.firstRequest_sound p a j hf
    have hai : a ≤ i := by
      by_contra hn
      have hia : i < a := lt_of_not_ge hn
      have hij := lt_trans hia ha.1.1
      have hhigh : high p j<high p i := by
        have hne : high p j≠high p i := fun h => (ne_of_lt hij)
          ((high_injective p h).symm)
        omega
      have hactive : Active p i j := ⟨hij,(high_lt_high p).mp hhigh⟩
      exact (not_le_of_gt hia) (ha.2 i hactive)
    simp only [SatClauseWireLattice.finishX,hf]
    dsimp [lane,low]
    omega

theorem side_intersection (j i : Fin N) (b : Bool) (e : Fin 6)
    (q : Point) (hq : q ∈SatClauseWireLattice.route p j b)
    (he : q ∈Sides.route p i e) :
    i=j ∧ SatClauseWireLattice.firstRequest? p j=none ∧
      q=SatClauseWireLattice.wirePoint p j b ∧
      ((if b then 7 else 4)=(XorGadget.arc (sideArc e)).1 ∨
       (if b then 7 else 4)=(XorGadget.arc (sideArc e)).2) := by
  have hc := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hb := SatClauseWireLattice.finishX_bounds p j
  have hs := Sides.route_segments p i e q he
  rcases hs with hs | hs
  · omega
  · have hij : i=j := by
      apply high_injective p
      cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega
    subst i
    obtain ⟨hf,hx⟩ := false_column_intersection p j q.1 hc.2.2 hs.1.symm.le
    have hp : q=SatClauseWireLattice.wirePoint p j b := by
      apply Prod.ext
      · simpa [SatClauseWireLattice.wirePoint,SatClauseWireLattice.finishX,hf] using hx
      · exact hc.1
    refine ⟨rfl,hf,hp,?_⟩
    rw [hp,SatClauseWireLattice.wire_endpoint_none p j hf b] at he
    exact (Sides.route_vertex_clear p j e _).mp he

private theorem offset_endpoint : ∀ (r : Fin 4) (b : Bool),
    offset r=(if b then -4 else 4) → r=(if b then 3 else 0) := by decide +kernel

theorem whole_intersection (j i : Fin N) (b : Bool) (r : Fin 4)
    (q : Point) (hq : q ∈SatClauseWireLattice.route p j b)
    (hr : q ∈Placement.route p (Residual.rowEnd p i) i r) :
    i=j ∧ SatClauseWireLattice.firstRequest? p j=none ∧
      r=(if b then 3 else 0) ∧ q=SatClauseWireLattice.wirePoint p j b := by
  have hc := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hl := lastInRow_before p _ i (Residual.rowEnd_valid p i)
  have hm := (whole_mem p _ i hl r q).mp hr
  have ho := offset_bounds r
  have hi := low_bounds i
  have hj := high_bounds p j
  rcases hm with hm | hm | hm
  · have hij : i=j := by
      apply high_injective p
      cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega
    subst i
    obtain ⟨hf,hx⟩ := false_column_intersection p j q.1 hc.2.2 hm.2.1
    refine ⟨rfl,hf,?_,?_⟩
    · have he : offset r=(if b then -4 else 4) := by
        cases b <;> dsimp [SatClauseWireLattice.height] at hc ⊢ <;> omega
      exact offset_endpoint r b he
    · apply Prod.ext
      · simpa [SatClauseWireLattice.wirePoint,SatClauseWireLattice.finishX,hf] using hx
      · exact hc.1
  · have hh : high p j≤high p i := by
      cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega
    have hx := finish_lt_lane p i j r hh
    omega
  · cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega

theorem residual_intersection (j : Fin N) (b : Bool) (v : Residual.Index p)
    (q : Point) (hq : q ∈SatClauseWireLattice.route p j b)
    (hv : q ∈Residual.route p v) :
    v.1=j ∧ SatClauseWireLattice.firstRequest? p j=none ∧
      v.2.1=(if b then 3 else 0) ∧ q=SatClauseWireLattice.wirePoint p j b :=
  whole_intersection p j v.1 b v.2.1 q hq
    (Residual.path_subset p _ v.1
      (lastInRow_before p _ v.1 (Residual.rowEnd_valid p v.1)) v.2.1 v.2.2 hv)

theorem wirePoint_mem (j : Fin N) (b : Bool) :
    SatClauseWireLattice.wirePoint p j b∈SatClauseWireLattice.route p j b := by
  rw [SatClauseWireLattice.route_mem]
  have hb := SatClauseWireLattice.finishX_bounds p j
  exact ⟨rfl,by dsimp [SatClauseWireLattice.wirePoint]; omega,le_rfl⟩

theorem wirePoint_endpoint (j : Fin N) (b : Bool) :
    (SatClauseWireLattice.route p j b).head?=some (SatClauseWireLattice.wirePoint p j b) ∨
    (SatClauseWireLattice.route p j b).getLast?=some (SatClauseWireLattice.wirePoint p j b) := by
  have he := SatClauseWireLattice.route_endpoints p j b
  cases b
  · exact Or.inr he.2
  · exact Or.inl he.1

theorem side_intersection_iff (j i : Fin N) (b : Bool) (e : Fin 6) (q : Point) :
    (q∈SatClauseWireLattice.route p j b ∧ q∈Sides.route p i e) ↔
      i=j ∧ SatClauseWireLattice.firstRequest? p j=none ∧
      q=SatClauseWireLattice.wirePoint p j b ∧
      ((if b then 7 else 4)=(XorGadget.arc (sideArc e)).1 ∨
       (if b then 7 else 4)=(XorGadget.arc (sideArc e)).2) := by
  constructor
  · rintro ⟨hq,he⟩
    exact side_intersection p j i b e q hq he
  · rintro ⟨rfl,hf,rfl,he⟩
    refine ⟨wirePoint_mem p i b,?_⟩
    rw [SatClauseWireLattice.wire_endpoint_none p i hf b]
    exact (Sides.route_vertex_clear p i e _).mpr he

/-- Shared points are actual list endpoints on both routes. -/
theorem side_endpoints (j i : Fin N) (b : Bool) (e : Fin 6)
    (q : Point) (hq : q ∈SatClauseWireLattice.route p j b)
    (he : q ∈Sides.route p i e) :
    ((SatClauseWireLattice.route p j b).head?=some q ∨
     (SatClauseWireLattice.route p j b).getLast?=some q) ∧
    ((Sides.route p i e).head?=some q ∨ (Sides.route p i e).getLast?=some q) := by
  obtain ⟨hij,hf,hp,hi⟩ := side_intersection p j i b e q hq he
  subst i
  constructor
  · simpa only [hp] using wirePoint_endpoint p j b
  · have hv : q=Sides.xorPoint p j (if b then 7 else 4) :=
      hp.trans (SatClauseWireLattice.wire_endpoint_none p j hf b)
    have hend := Sides.route_endpoints p j e
    rcases hi with hi | hi
    · exact Or.inl (hend.1.trans
        (congrArg some (hv.trans (congrArg (Sides.xorPoint p j) hi)).symm))
    · exact Or.inr (hend.2.trans
        (congrArg some (hv.trans (congrArg (Sides.xorPoint p j) hi)).symm))

/-- This covers the unsplit, upper, and lower residual constructors:
an intersection, if any, is a literal endpoint of each explicit list. -/
theorem residual_endpoints (j : Fin N) (b : Bool) (v : Residual.Index p)
    (q : Point) (hq : q ∈SatClauseWireLattice.route p j b)
    (hv : q ∈Residual.route p v) :
    ((SatClauseWireLattice.route p j b).head?=some q ∨
     (SatClauseWireLattice.route p j b).getLast?=some q) ∧
    ((Residual.route p v).head?=some q ∨ (Residual.route p v).getLast?=some q) := by
  obtain ⟨hij,hf,hr,hp⟩ := residual_intersection p j b v q hq hv
  constructor
  · simpa only [hp] using wirePoint_endpoint p j b
  · apply Sides.residual_outer_endpoint p v.1 v.2.1 v.2.2 q hv
    apply Or.inr
    have hq' := hp.trans (SatClauseWireLattice.wire_endpoint_none p j hf b)
    rw [hr,hij]
    convert hq' using 1
    cases b <;> rfl

/-- The lower residual portion never meets a clause link, including on
its own occurrence wire. -/
theorem lower_disjoint (j i k : Fin N) (b : Bool) (r : Fin 4)
    (hik : Active p i k) :
    (SatClauseWireLattice.route p j b).Disjoint
      (lower p (Residual.rowEnd p i) i k r) := by
  apply List.disjoint_left.mpr
  intro q hq hr
  have hc := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hl := lastInRow_before p _ i (Residual.rowEnd_valid p i)
  have hm := (lower_mem p _ i k hl hik r q).mp hr
  have ho := offset_bounds r
  have hi := low_bounds i
  have hj := high_bounds p j
  rcases hm with hm | hm
  · have hk := (high_lt_high p).mpr hik.2
    have hh : high p j≤high p i := by
      cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega
    have hx := finish_lt_lane p i j r hh
    omega
  · cases b <;> dsimp [SatClauseWireLattice.height] at hc <;> omega

theorem last_links_disjoint (j a i : Fin N) (b : Bool)
    (ha : Residual.rowEnd p i =some a) (e : Fin 66) (he : Links.LinkEdge e) :
    (SatClauseWireLattice.route p j b).Disjoint (SatCrossingLattice.route p (a,i) e) := by
  apply List.disjoint_left.mpr
  intro q hq hlink
  have hai := (Catalogue.lastRequest_sound p a i ha).1
  obtain ⟨hf,hi,hp⟩ := SatClauseWireLattice.active_box_intersection p j b (a,i) hai q hq
    (SatCrossingLattice.route_in_box p (a,i) e q hlink)
  dsimp only [Prod.fst,Prod.snd] at hf hi
  subst i
  have hc := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hb := Links.link_bounds p a j e he q hlink
  simp only [SatClauseWireLattice.finishX,hf] at hc
  omega

end GridHardness.SatClauseRetirementClearance
