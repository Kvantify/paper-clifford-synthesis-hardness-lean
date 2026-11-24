/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalInterface

/-!
# SAT Crossing Horizontal Routing

Horizontal routes for the two genuine inter-cell edges of an increasing
column sweep. The older cell contributes only its forty retained vertices.
The refreshed section zero is on the right, toward the variable endpoint.
-/

@[expose] public section

namespace GridHardness.SatCrossingHorizontal
open CliffordSynthesis PermutationWireLayout SatCrossingLattice SignedTentacle
set_option autoImplicit false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

/-- A long horizontal run, a six-step drop, and a ten-step final approach.
The small bend stays outside the next cell until the final port. -/
def bendPoint (a y : Int) (len k : Nat) : Point :=
  if k≤len then (a+k,y+10)
  else if k≤len+6 then (a+len,y+10-((k:Int)-len))
  else (a+len+((k:Int)-len-6),y+4)

def upperPath (a y : Int) (len : Nat) : List Point :=
  (List.range (len+17)).map (bendPoint a y len)

theorem bendPoint_injective (a y : Int) (len : Nat) : Function.Injective (bendPoint a y len) := by
  intro k l he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [bendPoint] at hx hy
  split_ifs at hx hy <;> omega

theorem upperPath_nodup (a y : Int) (len : Nat) : (upperPath a y len).Nodup :=
  List.Nodup.map (bendPoint_injective a y len) List.nodup_range

theorem upperPath_length (a y : Int) (len : Nat) : (upperPath a y len).length=len+17 := by
  simp [upperPath]

theorem upperPath_head (a y : Int) (len : Nat) :
    (upperPath a y len).head?=some (a,y+10) := by
  unfold upperPath
  rw [show len+17=(len+16)+1 by omega]
  simp [List.range_succ_eq_map,bendPoint]

theorem upperPath_last (a y : Int) (len : Nat) :
    (upperPath a y len).getLast?=some (a+len+10,y+4) := by
  simp only [upperPath,show len+17=(len+16)+1 by omega,List.range_succ,
    List.map_append,List.map_cons,List.map_nil,List.getLast?_append,List.getLast?_singleton]
  simp [bendPoint]

theorem upperPath_chain (a y : Int) (len : Nat) :
    (upperPath a y len).IsChain UnitStep := by
  rw [upperPath,List.isChain_map,List.isChain_range]
  intro k hk
  change IntegerGrid.manhattan (bendPoint a y len k) (bendPoint a y len (k+1))=1
  dsimp [bendPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem upperPath_bounds (a y : Int) (len : Nat) (q : Point)
    (hq : q ∈ upperPath a y len) :
    a≤q.1 ∧ q.1≤a+len+10 ∧ y+4≤q.2 ∧ q.2≤y+10 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [bendPoint]
  split_ifs <;> dsimp <;> omega

theorem upperPath_left (a y : Int) (len : Nat) (hl : 0 <len) (q : Point)
    (hq : q ∈ upperPath a y len) (hx : q.1 ≤a) : q=(a,y+10) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [bendPoint] at hx ⊢
  split_ifs at hx ⊢ <;> simp only [Prod.mk.injEq,and_true] at hx ⊢ <;> omega

theorem upperPath_right (a y : Int) (len : Nat) (q : Point)
    (hq : q ∈ upperPath a y len) (hx : a +len +10 ≤q.1) : q=(a+len+10,y+4) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [bendPoint] at hx ⊢
  split_ifs at hx ⊢ <;> simp only [Prod.mk.injEq,and_true] at hx ⊢ <;> omega

/-- Reflect the upper connection about the centreline to obtain the lower
connection; reversing it gives the correct directed edge. -/
def reflection (y : Int) : Frame := ⟨true,false,true,(0,2*y)⟩

theorem reflection_map (y : Int) (q : Point) : (reflection y).map q=(q.1,2*y-q.2) := by
  simp [reflection,Frame.map,OrthogonalTentacle.place,sign,sub_eq_add_neg]

def lowerPath (a y : Int) (len : Nat) : List Point :=
  ((upperPath a y len).map (reflection y).map).reverse

theorem lowerPath_head (a y : Int) (len : Nat) :
    (lowerPath a y len).head?=some (a+len+10,y-4) := by
  simp [lowerPath,List.head?_reverse,List.getLast?_map,upperPath_last,reflection_map]
  omega

theorem lowerPath_last (a y : Int) (len : Nat) :
    (lowerPath a y len).getLast?=some (a,y-10) := by
  simp [lowerPath,List.getLast?_reverse,List.head?_map,upperPath_head,reflection_map]
  omega

theorem lowerPath_nodup (a y : Int) (len : Nat) : (lowerPath a y len).Nodup := by
  rw [lowerPath,List.nodup_reverse]
  exact (upperPath_nodup a y len).map (reflection y).injective

theorem lowerPath_chain (a y : Int) (len : Nat) :
    (lowerPath a y len).IsChain UnitStep := by
  rw [lowerPath,List.isChain_reverse]
  apply List.isChain_map_of_isChain (reflection y).map _ (upperPath_chain a y len)
  intro q t h
  change IntegerGrid.manhattan _ _=1
  rw [(reflection y).distance]
  change IntegerGrid.manhattan _ _=1 at h
  dsimp [IntegerGrid.manhattan] at h ⊢
  omega

theorem lowerPath_length (a y : Int) (len : Nat) : (lowerPath a y len).length=len+17 := by
  simp [lowerPath,upperPath_length]

theorem lowerPath_bounds (a y : Int) (len : Nat) (q : Point)
    (hq : q ∈ lowerPath a y len) :
    a≤q.1 ∧ q.1≤a+len+10 ∧ y-10≤q.2 ∧ q.2≤y-4 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hq)
  have hh := upperPath_bounds a y len t ht
  rw [reflection_map]
  dsimp
  omega

theorem lowerPath_left (a y : Int) (len : Nat) (hl : 0 <len) (q : Point)
    (hq : q ∈ lowerPath a y len) (hx : q.1 ≤a) : q=(a,y-10) := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hq)
  rw [reflection_map] at hx ⊢
  have he := upperPath_left a y len hl t ht hx
  rw [he]
  apply Prod.ext
  · rfl
  · dsimp
    omega

theorem lowerPath_right (a y : Int) (len : Nat) (q : Point)
    (hq : q ∈ lowerPath a y len) (hx : a +len +10 ≤q.1) : q=(a+len+10,y-4) := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hq)
  rw [reflection_map] at hx ⊢
  have he := upperPath_right a y len t ht hx
  rw [he]
  apply Prod.ext
  · rfl
  · dsimp
    omega

variable {n : Nat} (p : Equiv.Perm (Fin n))

def gapLength (i k : Fin n) : Nat := (512*low k-75-(512*low i+45)).toNat

def upperRoute (i k j : Fin n) : List Point :=
  upperPath (512*low i+45) (512*high p j) (gapLength i k)

def lowerRoute (i k j : Fin n) : List Point :=
  lowerPath (512*low i+45) (512*high p j) (gapLength i k)

theorem gapLength_cast (i k : Fin n) (hik : i <k) :
    (gapLength i k : Int)=512*(low k-low i)-120 := by
  have hh := low_lt_low hik
  dsimp [gapLength]
  omega

theorem gapLength_pos (i k : Fin n) (hik : i <k) : 0<gapLength i k := by
  have hh := low_lt_low hik
  have hg := gapLength_cast i k hik
  omega

/-- The surviving row zero is to the right of all other retained vertices. -/
private theorem retained_local_bound : ∀ v : XorLine.Vertex 4, Retained v →
    20≤(XorLine.Lattice.point v).2 := by decide +kernel

theorem retained_bound (c : Cell n) (v : RetainedVertex) :
    (point p c v.val).1≤512*low c.1+45 := by
  have hh := retained_local_bound v.val v.property
  rw [point,frame_map]
  dsimp
  omega

theorem row_zero_coordinates (c : Cell n) :
    point p c (XorLine.row 0 false)=(512*low c.1+45,512*high p c.2+10) ∧
    point p c (XorLine.row 0 true)=(512*low c.1+45,512*high p c.2-10) := by
  have hh := SatCrossingRouting.row_port_coordinates p c 0
  simpa [XorLine.inputPort,XorLine.outputPort,SatCrossingRouting.lane,sub_eq_add_neg] using hh

/-- The actual directed edges from `incoming_interface` and
`outgoing_interface`, with their required old and new vertex endpoints. -/
theorem route_endpoints (i k j : Fin n) (hik : i <k) :
    (upperRoute p i k j).head?=some (point p (i,j) (XorLine.row 0 false)) ∧
    (upperRoute p i k j).getLast?=some
      (point p (k,j) (XorLine.inputPort 4 (.inl false))) ∧
    (lowerRoute p i k j).head?=some
      (point p (k,j) (XorLine.outputPort 4 (.inl false))) ∧
    (lowerRoute p i k j).getLast?=some (point p (i,j) (XorLine.row 0 true)) := by
  have hg := gapLength_cast i k hik
  have hr := row_zero_coordinates p (i,j)
  have hm := main_port_coordinates p (k,j)
  simp only [upperRoute,lowerRoute,upperPath_head,upperPath_last,lowerPath_head,lowerPath_last,
    hr.1,hr.2,hm.2.2.1,hm.2.2.2,Option.some.injEq,Prod.mk.injEq,true_and,and_true]
  constructor <;> omega

theorem route_simple (i k j : Fin n) :
    (upperRoute p i k j).Nodup ∧ (upperRoute p i k j).IsChain UnitStep ∧
    (lowerRoute p i k j).Nodup ∧ (lowerRoute p i k j).IsChain UnitStep :=
  ⟨upperPath_nodup _ _ _,upperPath_chain _ _ _,lowerPath_nodup _ _ _,lowerPath_chain _ _ _⟩

theorem route_lengths (i k j : Fin n) (hik : i <k) :
    ((upperRoute p i k j).length : Int)=512*(low k-low i)-103 ∧
    ((lowerRoute p i k j).length : Int)=512*(low k-low i)-103 := by
  have hg := gapLength_cast i k hik
  simp only [upperRoute,lowerRoute,upperPath_length,lowerPath_length]
  constructor <;> omega

theorem route_length_bounds (i k j : Fin n) (hik : i <k) :
    409≤(upperRoute p i k j).length ∧ (upperRoute p i k j).length≤512*n ∧
    409≤(lowerRoute p i k j).length ∧ (lowerRoute p i k j).length≤512*n := by
  have hl := route_lengths p i k j hik
  have hi := low_bounds i
  have hk := low_bounds k
  have hh := low_lt_low hik
  omega

theorem upperRoute_bounds (i k j : Fin n) (hik : i <k) (q : Point)
    (hq : q ∈ upperRoute p i k j) :
    512*low i+45≤q.1 ∧ q.1≤512*low k-65 ∧
      512*high p j+4≤q.2 ∧ q.2≤512*high p j+10 := by
  have hh := upperPath_bounds _ _ _ q hq
  have hg := gapLength_cast i k hik
  omega

theorem lowerRoute_bounds (i k j : Fin n) (hik : i <k) (q : Point)
    (hq : q ∈ lowerRoute p i k j) :
    512*low i+45≤q.1 ∧ q.1≤512*low k-65 ∧
      512*high p j-10≤q.2 ∧ q.2≤512*high p j-4 := by
  have hh := lowerPath_bounds _ _ _ q hq
  have hg := gapLength_cast i k hik
  omega

theorem pair_separated (i k j : Fin n) (hik : i <k) (q t : Point)
    (hq : q ∈ upperRoute p i k j) (ht : t ∈ lowerRoute p i k j) :
    8≤IntegerGrid.manhattan q t := by
  have hq' := upperRoute_bounds p i k j hik q hq
  have ht' := lowerRoute_bounds p i k j hik t ht
  dsimp [IntegerGrid.manhattan]
  omega

/-- The only old retained vertex touched is the appropriate row-zero port.
The deleted section-zero vertices are deliberately excluded. -/
theorem old_vertices_clear (i k j : Fin n) (hik : i <k) (v : RetainedVertex) :
    (point p (i,j) v.val ∈ upperRoute p i k j ↔ v.val=XorLine.row 0 false) ∧
    (point p (i,j) v.val ∈ lowerRoute p i k j ↔ v.val=XorLine.row 0 true) := by
  have hb := retained_bound p (i,j) v
  have hl := gapLength_pos i k hik
  have hr := row_zero_coordinates p (i,j)
  constructor
  · constructor
    · intro hq
      have he := upperPath_left _ _ _ hl _ hq hb
      rw [← hr.1] at he
      exact congrArg Prod.snd (@point_injective n p ((i,j),v.val) ((i,j),XorLine.row 0 false) he)
    · intro he
      rw [he]
      exact List.mem_of_head? (route_endpoints p i k j hik).1
  · constructor
    · intro hq
      have he := lowerPath_left _ _ _ hl _ hq hb
      rw [← hr.2] at he
      exact congrArg Prod.snd (@point_injective n p ((i,j),v.val) ((i,j),XorLine.row 0 true) he)
    · intro he
      rw [he]
      exact List.mem_of_getLast? (route_endpoints p i k j hik).2.2.2

/-- The next complete cell is touched only at its false input/output pair. -/
theorem new_vertices_clear (i k j : Fin n) (hik : i <k) (v : XorLine.Vertex 4) :
    (point p (k,j) v ∈ upperRoute p i k j ↔ v=XorLine.inputPort 4 (.inl false)) ∧
    (point p (k,j) v ∈ lowerRoute p i k j ↔ v=XorLine.outputPort 4 (.inl false)) := by
  have hb := point_in_box p (k,j) v
  have hg := gapLength_cast i k hik
  have hx : 512*low i+45+(gapLength i k:Int)+10≤(point p (k,j) v).1 := by
    dsimp [InBox] at hb
    omega
  have hm := main_port_coordinates p (k,j)
  have he : 512*low i+45+(gapLength i k:Int)+10=512*low k-65 := by omega
  constructor
  · constructor
    · intro hq
      have hh := upperPath_right _ _ _ _ hq hx
      rw [he,← hm.2.2.1] at hh
      exact congrArg Prod.snd (@point_injective n p ((k,j),v)
        ((k,j),XorLine.inputPort 4 (.inl false)) hh)
    · intro hh
      rw [hh]
      exact List.mem_of_getLast? (route_endpoints p i k j hik).2.1
  · constructor
    · intro hq
      have hh := lowerPath_right _ _ _ _ hq hx
      rw [he,← hm.2.2.2] at hh
      exact congrArg Prod.snd (@point_injective n p ((k,j),v)
        ((k,j),XorLine.outputPort 4 (.inl false)) hh)
    · intro hh
      rw [hh]
      exact List.mem_of_head? (route_endpoints p i k j hik).2.2.1

theorem route_bounds (i k j : Fin n) (hik : i <k) (q : Point)
    (hq : q ∈ upperRoute p i k j ∨ q ∈ lowerRoute p i k j) :
    512*low i+45≤q.1 ∧ q.1≤512*low k-65 ∧
      512*high p j-10≤q.2 ∧ q.2≤512*high p j+10 := by
  rcases hq with hq | hq
  · have hh := upperRoute_bounds p i k j hik q hq
    omega
  · have hh := lowerRoute_bounds p i k j hik q hq
    omega

/-- The horizontal connections retain the same linear global coordinate
bound as the crossing cells and the vertical connections. -/
theorem route_coordinates_bounded (i k j : Fin n) (hik : i <k) (q : Point)
    (hq : q ∈ upperRoute p i k j ∨ q ∈ lowerRoute p i k j) :
    0≤q.1 ∧ q.1≤512*n+65 ∧ 0≤q.2 ∧ q.2≤1024*n+522 := by
  have hq' := route_bounds p i k j hik q hq
  have hi := low_bounds i
  have hk := low_bounds k
  have hj := high_bounds p j
  omega

/-- Consecutive active inversion columns in one horizontal row. This is a
finite combinatorial condition, not an assumed planar embedding. -/
def ConsecutiveColumns (i k j : Fin n) : Prop :=
  SatCrossingRouting.Active p i j ∧ SatCrossingRouting.Active p k j ∧ i<k ∧
    ∀ a, SatCrossingRouting.Active p a j → i<a → k≤a

theorem other_box_separated (i k j : Fin n) (hc : ConsecutiveColumns p i k j)
    (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (hdi : d ≠(i, j)) (hdk : d ≠(k, j)) (q t : Point)
    (hq : q ∈ upperRoute p i k j ∨ q ∈ lowerRoute p i k j) (ht : InBox p d t) :
    492≤IntegerGrid.manhattan q t := by
  have hq' := route_bounds p i k j hc.2.2.1 q hq
  dsimp [InBox] at ht
  dsimp [IntegerGrid.manhattan]
  by_cases hj : d.2=j
  · have hi : d.1≠i := fun h => hdi (Prod.ext h hj)
    have hk : d.1≠k := fun h => hdk (Prod.ext h hj)
    rcases lt_or_gt_of_ne hi with hlo | hhi
    · have hh := low_lt_low hlo
      omega
    · have hle := hc.2.2.2 d.1 (by simpa [hj] using hd) hhi
      have hh := low_lt_low (lt_of_le_of_ne hle hk.symm)
      omega
  · have hh : high p d.2≠high p j := fun h => hj (high_injective p h)
    omega

end GridHardness.SatCrossingHorizontal
