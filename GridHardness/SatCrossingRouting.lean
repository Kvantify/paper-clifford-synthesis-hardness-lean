/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingLattice

/-!
# SAT Crossing Routing

Explicit routes between consecutive crossing boxes in the same wire
column. The four mandatory arcs have alternating directions, so half of the
routes run downwards. These statements concern the actual boundary ports of
`XorLine`, and do not assume an embedding of the complete SAT graph.
-/

@[expose] public section

namespace GridHardness.SatCrossingRouting
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

/-- An inclusive upwards unit-step route of the stated height. -/
def rising (x y : Int) (height : Nat) : List Point :=
  (List.range (height+1)).map (fun k : Nat => (x,y+(k:Int)))

theorem rising_length (x y : Int) (height : Nat) :
    (rising x y height).length = height+1 := by simp [rising]

theorem rising_nodup (x y : Int) (height : Nat) : (rising x y height).Nodup := by
  apply List.Nodup.map _ (List.nodup_range)
  intro a b h
  have hh := congrArg Prod.snd h
  dsimp at hh
  omega

theorem rising_mem (x y : Int) (height : Nat) (q : Point) :
    q ∈ rising x y height ↔ q.1=x ∧ y ≤ q.2 ∧ q.2 ≤ y+height := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    exact ⟨rfl,by omega,by omega⟩
  · rintro ⟨hx,hl,hu⟩
    apply List.mem_map.mpr
    refine ⟨(q.2-y).toNat,?_,?_⟩
    · simp only [List.mem_range]
      omega
    · apply Prod.ext <;> dsimp <;> omega

theorem rising_head (x y : Int) (height : Nat) :
    (rising x y height).head? = some (x,y) := by
  simp [rising, List.range_succ_eq_map]

theorem rising_last (x y : Int) (height : Nat) :
    (rising x y height).getLast? = some (x,y+height) := by
  simp [rising, List.range_succ]

theorem rising_chain (x y : Int) (height : Nat) :
    (rising x y height).IsChain UnitStep := by
  rw [rising, List.isChain_map, List.isChain_range]
  intro k hk
  change IntegerGrid.manhattan (x,y+(k:Int)) (x,y+(k+1:Int)) = 1
  dsimp [IntegerGrid.manhattan]
  omega

private theorem unitStep_symm {a b : Point} (h : UnitStep a b) : UnitStep b a := by
  change IntegerGrid.manhattan _ _ = 1 at h ⊢
  dsimp [IntegerGrid.manhattan] at h ⊢
  omega

variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- The horizontal position of the row lane within a rotated crossing box. -/
def lane (i : Fin n) (r : Fin 4) : Int := 512*low i+45-30*(r.val:Int)

theorem row_port_coordinates (c : Cell n) (r : Fin 4) :
    point p c (XorLine.inputPort 4 (.inr r)) =
      (lane c.1 r,512*high p c.2 + if r.val%2=0 then 10 else -10) ∧
    point p c (XorLine.outputPort 4 (.inr r)) =
      (lane c.1 r,512*high p c.2 + if r.val%2=0 then -10 else 10) := by
  obtain ⟨hi,ho⟩ := XorLine.Lattice.row_port_coordinates r
  unfold point
  rw [hi,ho,frame_map,frame_map]
  dsimp [lane]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- Four distinct parallel lanes, at distance at least thirty. -/
theorem lane_separated (i : Fin n) (r s : Fin 4) (hrs : r ≠s) :
    30 ≤ |lane i r-lane i s| := by
  have hh : r.val≠s.val := fun h => hrs (Fin.ext h)
  dsimp [lane]
  by_cases h : 0 ≤ 512*low i+45-30*(r.val:Int)-(512*low i+45-30*(s.val:Int))
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_neg (by omega)]
    omega

/-- The undirected geometric segment from the upper side of the lower box
to the lower side of the higher box. -/
def corridor (i j k : Fin n) (r : Fin 4) : List Point :=
  rising (lane i r) (512*high p j+10) ((512*high p k-10-(512*high p j+10)).toNat)

/-- Orient the segment from the relevant output port to the next input port.
Even rows point downwards and odd rows point upwards. -/
def route (i j k : Fin n) (r : Fin 4) : List Point :=
  if r.val%2=0 then (corridor p i j k r).reverse else corridor p i j k r

theorem corridor_mem (i j k : Fin n) (hjk : p j <p k) (r : Fin 4) (q : Point) :
    q ∈ corridor p i j k r ↔
      q.1=lane i r ∧ 512*high p j+10 ≤ q.2 ∧ q.2 ≤ 512*high p k-10 := by
  have hh := (high_lt_high p).mpr hjk
  rw [corridor, rising_mem]
  constructor <;> rintro ⟨hx,hl,hu⟩ <;> refine ⟨hx,hl,?_⟩ <;> omega

theorem route_mem (i j k : Fin n) (hjk : p j <p k) (r : Fin 4) (q : Point) :
    q ∈ route p i j k r ↔
      q.1=lane i r ∧ 512*high p j+10 ≤ q.2 ∧ q.2 ≤ 512*high p k-10 := by
  unfold route
  split_ifs <;> simp only [List.mem_reverse, corridor_mem p i j k hjk]

theorem route_nodup (i j k : Fin n) (r : Fin 4) :
    (route p i j k r).Nodup := by
  unfold route
  split_ifs
  · rw [List.nodup_reverse]
    exact rising_nodup _ _ _
  · exact rising_nodup _ _ _

theorem route_chain (i j k : Fin n) (r : Fin 4) :
    (route p i j k r).IsChain UnitStep := by
  unfold route
  split_ifs
  · apply List.isChain_reverse.mpr
    exact (rising_chain _ _ _).imp (fun _ _ h => unitStep_symm h)
  · exact rising_chain _ _ _

theorem route_length (i j k : Fin n) (hjk : p j <p k) (r : Fin 4) :
    ((route p i j k r).length : Int) = 512*(high p k-high p j)-19 := by
  have hh := (high_lt_high p).mpr hjk
  unfold route
  split_ifs <;> simp only [List.length_reverse, corridor, rising_length] <;> omega

theorem route_length_bounds (i j k : Fin n) (hjk : p j <p k) (r : Fin 4) :
    493 ≤ (route p i j k r).length ∧ (route p i j k r).length ≤ 512*n := by
  have hl := route_length p i j k hjk r
  have hj := high_bounds p j
  have hk := high_bounds p k
  have hh := (high_lt_high p).mpr hjk
  dsimp [high] at hl
  have hj' := (p j).isLt
  have hk' := (p k).isLt
  omega

theorem route_endpoints (i j k : Fin n) (hjk : p j <p k) (r : Fin 4) :
    (route p i j k r).head? = some
      (point p (i,if r.val%2=0 then k else j) (XorLine.outputPort 4 (.inr r))) ∧
    (route p i j k r).getLast? = some
      (point p (i,if r.val%2=0 then j else k) (XorLine.inputPort 4 (.inr r))) := by
  have hh := (high_lt_high p).mpr hjk
  have ht : (512*high p k-10-(512*high p j+10)).toNat =
      512*high p k-10-(512*high p j+10) := by omega
  have hlo := row_port_coordinates p (i,j) r
  have hhi := row_port_coordinates p (i,k) r
  unfold route corridor
  by_cases he : r.val%2=0
  · simp only [he, ite_true, List.head?_reverse, List.getLast?_reverse,
      rising_head, rising_last, ht, hhi.2, hlo.1]
    simp only [Prod.mk.injEq, true_and, Option.some.injEq]
    simp only [and_true]
    omega
  · simp only [he, ite_false, rising_head, rising_last, ht, hlo.2, hhi.1]
    simp only [Prod.mk.injEq, true_and, Option.some.injEq]
    omega

/-- Separate lanes never meet, including their endpoints. -/
theorem routes_separated (i j k : Fin n) (hjk : p j <p k) (r s : Fin 4) (hrs : r ≠s)
    (q t : Point) (hq : q ∈ route p i j k r) (ht : t ∈ route p i j k s) :
    30 ≤ IntegerGrid.manhattan q t := by
  have hq' := (route_mem p i j k hjk r q).mp hq
  have ht' := (route_mem p i j k hjk s t).mp ht
  have hr := lane_separated i r s hrs
  dsimp [IntegerGrid.manhattan]
  rw [hq'.1,ht'.1]
  have hab := Int.natCast_natAbs (lane i r-lane i s)
  omega

/-- The actual inversion condition, independent of any geometric hypotheses. -/
def Active (i j : Fin n) : Prop := i<j ∧ p j<p i
instance (i j : Fin n) : Decidable (Active p i j) := inferInstanceAs (Decidable (_ ∧ _))

theorem active_iff_mem (i j : Fin n) : Active p i j ↔ (i,j) ∈ crossings p := by
  simp [Active,crossings]

/-- Consecutive active cells, ordered by the height of the second wire. -/
def Consecutive (i j k : Fin n) : Prop :=
  Active p i j ∧ Active p i k ∧ p j<p k ∧
    ∀ l, Active p i l → p j<p l → p k≤p l

/-- Candidate successor heights, computed directly from the permutation. -/
def nextRanks (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun h => Active p i (p.symm h) ∧ p j<h)

def next? (i j : Fin n) : Option (Fin n) :=
  if h : (nextRanks p i j).Nonempty then some (p.symm ((nextRanks p i j).min' h)) else none

theorem next_sound (i j k : Fin n) (hj : Active p i j) (hk : next? p i j =some k) :
    Consecutive p i j k := by
  unfold next? at hk
  split at hk
  next h =>
    have he := Option.some.inj hk
    subst k
    have hm := Finset.min'_mem (nextRanks p i j) h
    have hm' := (Finset.mem_filter.mp hm).2
    refine ⟨hj,hm'.1,by simpa only [Equiv.apply_symm_apply] using hm'.2,?_⟩
    intro l hl hjl
    simp only [Equiv.apply_symm_apply]
    apply Finset.min'_le
    simp [nextRanks, hl, hjl]
  next h => contradiction

theorem next_exists (i j : Fin n) (k : Fin n) (hk : Active p i k) (hjk : p j <p k) :
    ∃ l, next? p i j=some l := by
  have hn : (nextRanks p i j).Nonempty := by
    refine ⟨p k,?_⟩
    simp [nextRanks,hk,hjk]
  simp [next?,hn]

/-- An inter-cell route meets no other active crossing box. The clearance is
proved from consecutive positions in the actual permutation catalogue. -/
theorem route_other_box_clear (i j k : Fin n) (hc : Consecutive p i j k) (r : Fin 4)
    (d : Cell n) (hd : Active p d.1 d.2) (hdj : d ≠(i, j)) (hdk : d ≠(i, k))
    (q : Point) (hq : q ∈ route p i j k r) : ¬ InBox p d q := by
  intro hb
  have hq' := (route_mem p i j k hc.2.2.1 r q).mp hq
  dsimp [InBox] at hb
  have hr := r.isLt
  by_cases hi : d.1=i
  · have hj : d.2≠j := fun h => hdj (Prod.ext hi h)
    have hk : d.2≠k := fun h => hdk (Prod.ext hi h)
    have hj' : high p d.2≠high p j := fun h => hj (high_injective p h)
    have hk' : high p d.2≠high p k := fun h => hk (high_injective p h)
    have hlo : p j<p d.2 := (high_lt_high p).mp (by omega)
    have hle := hc.2.2.2 d.2 (by simpa [hi] using hd) hlo
    have hhe : high p k ≤ high p d.2 := by dsimp [high]; omega
    omega
  · have hh : low d.1≠low i := fun h => hi (low_injective h)
    dsimp [lane] at hq'
    omega

/-- Endpoint boxes are touched exactly at the intended row boundary points. -/
theorem route_endpoint_boxes (i j k : Fin n) (hjk : p j <p k) (r : Fin 4)
    (q : Point) (hq : q ∈ route p i j k r) :
    (InBox p (i,j) q ↔ q=(lane i r,512*high p j+10)) ∧
    (InBox p (i,k) q ↔ q=(lane i r,512*high p k-10)) := by
  have hq' := (route_mem p i j k hjk r q).mp hq
  have hr := r.isLt
  dsimp [InBox]
  constructor
  · constructor
    · intro hb
      apply Prod.ext hq'.1
      dsimp
      omega
    · rintro rfl
      dsimp [lane]
      omega
  · constructor
    · intro hb
      apply Prod.ext hq'.1
      dsimp
      omega
    · rintro rfl
      dsimp [lane]
      omega

theorem next_none_iff (i j : Fin n) :
    next? p i j=none ↔ ∀ k, Active p i k → p k≤p j := by
  constructor
  · intro hn k hk
    by_contra hle
    obtain ⟨l,hl⟩ := next_exists p i j k hk (by omega)
    rw [hn] at hl
    contradiction
  · intro h
    unfold next?
    split
    next hn =>
      obtain ⟨r,hr⟩ := hn
      have hm := (Finset.mem_filter.mp hr).2
      have hh := h (p.symm r) hm.1
      simp only [Equiv.apply_symm_apply] at hh
      omega
    next hn => rfl

/-- Distinct consecutive gaps in a column have disjoint height intervals. -/
theorem consecutive_order (i j k l m : Fin n)
    (hjk : Consecutive p i j k) (hlm : Consecutive p i l m) (hjl : j ≠l) :
    p k≤p l ∨ p m≤p j := by
  have hh : p j≠p l := fun h => hjl (p.injective h)
  rcases lt_or_gt_of_ne hh with h | h
  · exact Or.inl (hjk.2.2.2 l hlm.1 h)
  · exact Or.inr (hlm.2.2.2 j hjk.1 h)

theorem consecutive_unique (i j k m : Fin n)
    (hjk : Consecutive p i j k) (hjm : Consecutive p i j m) : k=m := by
  apply p.injective
  exact le_antisymm (hjk.2.2.2 m hjm.2.1 hjm.2.2.1)
    (hjm.2.2.2 k hjk.2.1 hjk.2.2.1)

/-- Different wire columns leave a wide horizontal gap between all their
routes, regardless of the chosen heights or lanes. -/
theorem different_columns_separated (i j k a b c : Fin n) (hia : i ≠a)
    (hjk : p j <p k) (hbc : p b <p c) (r s : Fin 4) (q t : Point)
    (hq : q ∈ route p i j k r) (ht : t ∈ route p a b c s) :
    422 ≤ IntegerGrid.manhattan q t := by
  have hq' := (route_mem p i j k hjk r q).mp hq
  have ht' := (route_mem p a b c hbc s t).mp ht
  have hh : low i≠low a := fun h => hia (low_injective h)
  have hr := r.isLt
  have hs := s.isLt
  dsimp [lane] at hq' ht'
  dsimp [IntegerGrid.manhattan]
  omega

/-- Different consecutive gaps remain separated by the height of the
intervening box, even when they use the same row lane. -/
theorem different_gaps_separated (i j k l m : Fin n)
    (hjk : Consecutive p i j k) (hlm : Consecutive p i l m) (hjl : j ≠l)
    (r s : Fin 4) (q t : Point)
    (hq : q ∈ route p i j k r) (ht : t ∈ route p i l m s) :
    20 ≤ IntegerGrid.manhattan q t := by
  have hq' := (route_mem p i j k hjk.2.2.1 r q).mp hq
  have ht' := (route_mem p i l m hlm.2.2.1 s t).mp ht
  have hh := consecutive_order p i j k l m hjk hlm hjl
  dsimp [IntegerGrid.manhattan]
  rcases hh with h | h
  · have hhl : high p k≤high p l := by dsimp [high]; omega
    omega
  · have hhm : high p m≤high p j := by dsimp [high]; omega
    omega

/-- Every pair of distinct routes in the complete vertical connection family
is separated by at least twenty grid steps. In particular there are neither
shared vertices nor accidental edges between different routes. -/
theorem global_separation (i j k a b c : Fin n) (r s : Fin 4)
    (hjk : Consecutive p i j k) (hbc : Consecutive p a b c)
    (hd : (i, j, k, r) ≠(a, b, c, s)) (q t : Point)
    (hq : q ∈ route p i j k r) (ht : t ∈ route p a b c s) :
    20 ≤ IntegerGrid.manhattan q t := by
  by_cases hi : i=a
  · subst a
    by_cases hj : j=b
    · subst b
      have hk := consecutive_unique p i j k c hjk hbc
      subst c
      have hr : r≠s := by intro h; subst s; exact hd rfl
      exact (by omega : 20≤30).trans (routes_separated p i j k hjk.2.2.1 r s hr q t hq ht)
    · exact different_gaps_separated p i j k b c hjk hbc hj r s q t hq ht
  · exact (by omega : 20≤422).trans
      (different_columns_separated p i j k a b c hi hjk.2.2.1 hbc.2.2.1 r s q t hq ht)

/-- Every connection stays in the same linear coordinate bound as its two
crossing boxes. -/
theorem route_coordinates_bounded (i j k : Fin n) (hjk : p j <p k) (r : Fin 4)
    (q : Point) (hq : q ∈ route p i j k r) :
    0 ≤ q.1 ∧ q.1≤512*n+65 ∧ 0≤q.2 ∧ q.2≤1024*n+522 := by
  have hq' := (route_mem p i j k hjk r q).mp hq
  have hi := low_bounds i
  have hj := high_bounds p j
  have hk := high_bounds p k
  have hr := r.isLt
  dsimp [lane] at hq'
  omega

/-- Clearance from unrelated active boxes is quantitative, so these routes
cannot create unintended unit-grid adjacencies with another local gadget. -/
theorem other_box_separated (i j k : Fin n) (hc : Consecutive p i j k) (r : Fin 4)
    (d : Cell n) (hd : Active p d.1 d.2) (hdj : d ≠(i, j)) (hdk : d ≠(i, k))
    (q t : Point) (hq : q ∈ route p i j k r) (ht : InBox p d t) :
    402 ≤ IntegerGrid.manhattan q t := by
  have hq' := (route_mem p i j k hc.2.2.1 r q).mp hq
  have hr := r.isLt
  dsimp [InBox] at ht
  dsimp [IntegerGrid.manhattan]
  by_cases hi : d.1=i
  · have hj : d.2≠j := fun h => hdj (Prod.ext hi h)
    have hk : d.2≠k := fun h => hdk (Prod.ext hi h)
    have hj' : p d.2≠p j := fun h => hj (p.injective h)
    have hk' : p d.2≠p k := fun h => hk (p.injective h)
    rcases lt_or_gt_of_ne hj' with hlo | hhi
    · have hh := (high_lt_high p).mpr hlo
      omega
    · have hle := hc.2.2.2 d.2 (by simpa [hi] using hd) hhi
      have hh := (high_lt_high p).mpr (lt_of_le_of_ne hle hk'.symm)
      omega
  · have hh : low d.1≠low i := fun h => hi (low_injective h)
    dsimp [lane] at hq'
    omega

/-- Which directed row vertex occupies the positive vertical boundary. -/
def lowerPort (r : Fin 4) : XorLine.Vertex 4 :=
  if r.val%2=0 then XorLine.inputPort 4 (.inr r) else XorLine.outputPort 4 (.inr r)

/-- Which directed row vertex occupies the negative vertical boundary. -/
def upperPort (r : Fin 4) : XorLine.Vertex 4 :=
  if r.val%2=0 then XorLine.outputPort 4 (.inr r) else XorLine.inputPort 4 (.inr r)

theorem lowerPort_coordinates (i j : Fin n) (r : Fin 4) :
    point p (i,j) (lowerPort r) = (lane i r,512*high p j+10) := by
  have hp := row_port_coordinates p (i,j) r
  by_cases h : r.val%2=0 <;> simp [lowerPort,h,hp.1,hp.2]

theorem upperPort_coordinates (i j : Fin n) (r : Fin 4) :
    point p (i,j) (upperPort r) = (lane i r,512*high p j-10) := by
  have hp := row_port_coordinates p (i,j) r
  by_cases h : r.val%2=0 <;> simp [upperPort,h,hp.1,hp.2] <;> omega

/-- Every vertical connecting route contains exactly its two row-port
vertices among all vertices of active crossing gadgets. -/
theorem route_vertex_clear (i j k : Fin n) (hc : Consecutive p i j k) (r : Fin 4)
    (d : Cell n) (hd : Active p d.1 d.2) (v : XorLine.Vertex 4) :
    point p d v ∈ route p i j k r ↔
      (d=(i,j) ∧ v=lowerPort r) ∨ (d=(i,k) ∧ v=upperPort r) := by
  constructor
  · intro hq
    by_cases hj : d=(i,j)
    · subst d
      have he := ((route_endpoint_boxes p i j k hc.2.2.1 r _ hq).1).mp (point_in_box p _ _)
      rw [← lowerPort_coordinates p i j r] at he
      have hv := @point_injective n p ((i,j),v) ((i,j),lowerPort r) he
      exact Or.inl ⟨rfl,congrArg Prod.snd hv⟩
    · by_cases hk : d=(i,k)
      · subst d
        have he := ((route_endpoint_boxes p i j k hc.2.2.1 r _ hq).2).mp (point_in_box p _ _)
        rw [← upperPort_coordinates p i k r] at he
        have hv := @point_injective n p ((i,k),v) ((i,k),upperPort r) he
        exact Or.inr ⟨rfl,congrArg Prod.snd hv⟩
      · exact False.elim (route_other_box_clear p i j k hc r d hd hj hk _ hq (point_in_box p _ _))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rw [lowerPort_coordinates,route_mem p i j k hc.2.2.1]
      have hh := (high_lt_high p).mpr hc.2.2.1
      exact ⟨rfl,le_rfl,by omega⟩
    · rw [upperPort_coordinates,route_mem p i j k hc.2.2.1]
      have hh := (high_lt_high p).mpr hc.2.2.1
      exact ⟨rfl,by omega,le_rfl⟩

end GridHardness.SatCrossingRouting
