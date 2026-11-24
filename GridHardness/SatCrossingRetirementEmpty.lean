/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementSegments

/-!
# SAT Crossing Retirement Empty

The unsplit residual lane when a retired wire has no future crossings.
Its geometric clearance follows from the actual empty inversion column.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Segments
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false
variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- An explicit three-segment characterization of the unsplit retired lane. -/
theorem whole_mem (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r : Fin 4) (q : Point) :
    q∈Placement.route p last i r ↔
      (q.2=512*high p i+offset r ∧ Placement.left last≤q.1 ∧ q.1≤SatCrossingRouting.lane i r) ∨
      (q.1=SatCrossingRouting.lane i r ∧ 512*low i+offset r≤q.2 ∧ q.2≤512*high p i+offset r) ∨
      (q.2=512*low i+offset r ∧ SatCrossingRouting.lane i r≤q.1 ∧ q.1≤512*((n:Int)+1)+65) := by
  have hp := Placement.parameters p last i hl
  have ht := turn_cast (Placement.span last i) hp.2.1 r
  have hm (t : Point) : t∈SatCrossingRetirement.route (Placement.span last i)
      (Placement.height p i) (Placement.tail i) r ↔
      (t.2=(Placement.height p i:Int)+offset r ∧ 0≤t.1 ∧ t.1≤turn (Placement.span last i) r) ∨
      (t.1=(turn (Placement.span last i) r:Int) ∧ offset r≤t.2 ∧ t.2≤(Placement.height p i:Int)+offset r) ∨
      (t.2=offset r ∧ (turn (Placement.span last i) r:Int)≤t.1 ∧ t.1≤finish (Placement.span last i) (Placement.tail i)) := by
    rw [SatCrossingRetirement.route_mem,path_mem _ _ _ hp.2.1]
  constructor
  · intro hq
    obtain ⟨t,htq,rfl⟩ := List.mem_map.mp hq
    rw [Placement.frame_map]
    have hh := (hm t).mp htq
    dsimp [SatCrossingRouting.lane,finish] at hh ⊢
    rcases hh with hh | hh | hh
    · exact Or.inl ⟨by omega,by omega,by omega⟩
    · exact Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)
  · intro hq
    apply List.mem_map.mpr
    refine ⟨(q.1-Placement.left last,q.2-512*low i),?_,?_⟩
    · rw [hm]
      dsimp [SatCrossingRouting.lane,finish] at hq ⊢
      rcases hq with hq | hq | hq
      · exact Or.inl ⟨by omega,by omega,by omega⟩
      · exact Or.inr (Or.inl ⟨by omega,by omega,by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)
    · rw [Placement.frame_map]
      apply Prod.ext <;> dsimp <;> omega

def EmptyColumn (i : Fin n) : Prop := ∀ j, ¬SatCrossingRouting.Active p i j

/-- With no future crossing in its column, the complete retirement route
misses every active crossing box except the one containing its false endpoint. -/
theorem whole_other_box_clear (last : Option (Fin n)) (i : Fin n)
    (hl : LastInRow p last i) (he : EmptyColumn p i) (r : Fin 4)
    (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (hprev : last ≠some d.1 ∨ d.2 ≠i) (q : Point)
    (hq : q ∈Placement.route p last i r) : ¬InBox p d q := by
  intro hb
  have hm := (whole_mem p last i (lastInRow_before p last i hl) r q).mp hq
  have ho := offset_bounds r
  have hr := r.isLt
  dsimp [InBox] at hb
  rcases hm with ⟨hy,hx,hz⟩ | ⟨hx,hy,hz⟩ | ⟨hy,hx,hz⟩
  · have hdi : d.2=i := by
      apply high_injective p
      omega
    have hd' : SatCrossingRouting.Active p d.1 i := by simpa [hdi] using hd
    cases last with
    | none => exact hl d.1 hd'
    | some a =>
      have hle := hl.2 d.1 hd'
      have hne : a≠d.1 := by simpa [hdi] using hprev
      have hlt : d.1<a := lt_of_le_of_ne hle (Ne.symm hne)
      have hh := low_lt_low hlt
      dsimp [Placement.left] at hx
      omega
  · have hdi : d.1=i := by
      apply low_injective
      dsimp [SatCrossingRouting.lane] at hx
      omega
    exact he d.2 (by simpa [hdi] using hd)
  · have hi := low_bounds i
    have hh := high_bounds p d.2
    omega

/-- Clearance at the last horizontal tile uses the forty vertices that
actually survive retirement, not all forty-eight original tile vertices. -/
theorem whole_latest_retained_clear (a i : Fin n) (hai : a < i) (r : Fin 4)
    (v : SatCrossingHorizontal.RetainedVertex) :
    point p (a,i) v.val ∉ Placement.route p (some a) i r := by
  intro hq
  have hm := (whole_mem p (some a) i (by intro k hk; cases hk; exact hai) r _).mp hq
  have hb := SatCrossingHorizontal.retained_bound p (a,i) v
  dsimp only [Prod.fst] at hb
  have hh := low_lt_low hai
  have hr := r.isLt
  dsimp [Placement.left,SatCrossingRouting.lane] at hm
  rcases hm with hm | hm | hm <;> omega

/-- No retained active-crossing vertex lies on a retirement lane whose
column has no crossings. The lane's eight retired XOR endpoints are separate. -/
theorem whole_retained_vertex_clear (last : Option (Fin n)) (i : Fin n)
    (hl : LastInRow p last i) (he : EmptyColumn p i) (r : Fin 4)
    (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (v : SatCrossingHorizontal.RetainedVertex) :
    point p d v.val ∉ Placement.route p last i r := by
  intro hv
  by_cases hh : last=some d.1 ∧ d.2=i
  · obtain ⟨hh,hi⟩ := hh
    have hdi := lastInRow_before p last i hl d.1 hh
    change point p (d.1,d.2) v.val∈Placement.route p last i r at hv
    rw [hh,hi] at hv
    exact whole_latest_retained_clear p d.1 i hdi r v hv
  · have hh' : last≠some d.1 ∨ d.2≠i := by tauto
    exact whole_other_box_clear p last i hl he r d hd hh' _ hv (point_in_box p d v.val)

end GridHardness.SatCrossingRetirement.Segments
