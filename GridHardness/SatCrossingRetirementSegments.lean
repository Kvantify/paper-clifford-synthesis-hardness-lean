/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementRouting
public import GridHardness.SatCrossingHorizontalRouting

/-!
# SAT Crossing Retirement Segments

Residual ends of a retired XOR lane after its vertical crossings have
been inserted. The paths are explicit slices of the already verified bend
route; their endpoints are the actual row ports of the crossing cells.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Segments
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false

/-- Index of a point in the vertical part of an un-oriented retirement path. -/
def cut (span height : Nat) (r : Fin 4) (y : Int) : Nat :=
  ((turn span r:Int)+height+offset r-y).toNat

def headPath (span height : Nat) (r : Fin 4) (y : Int) : List Point :=
  (List.range (cut span height r y+1)).map (pathPoint span height r)

def tailPath (span height tail : Nat) (r : Fin 4) (y : Int) : List Point :=
  (List.range (finish span tail+height-cut span height r y+1)).map
    (fun k => pathPoint span height r (k+cut span height r y))

theorem cut_bounds (span height : Nat) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    turn span r≤cut span height r y ∧ cut span height r y≤turn span r+height ∧
    (cut span height r y:Int)=(turn span r:Int)+height+offset r-y := by
  dsimp [cut]
  omega

theorem cut_point (span height : Nat) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    pathPoint span height r (cut span height r y)=((turn span r:Int),y) := by
  have hc := cut_bounds span height r y hy
  dsimp [pathPoint]
  split_ifs <;> apply Prod.ext <;> dsimp <;> omega

private theorem pathPoint_step (span height : Nat) (r : Fin 4) (k : Nat) :
    UnitStep (pathPoint span height r k) (pathPoint span height r (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [pathPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem headPath_simple (span height : Nat) (r : Fin 4) (y : Int) :
    (headPath span height r y).Nodup ∧ (headPath span height r y).IsChain UnitStep := by
  constructor
  · exact List.Nodup.map (pathPoint_injective span height r) List.nodup_range
  · rw [headPath,List.isChain_map,List.isChain_range]
    intro k hk
    exact pathPoint_step span height r k

theorem tailPath_simple (span height tail : Nat) (r : Fin 4) (y : Int) :
    (tailPath span height tail r y).Nodup ∧ (tailPath span height tail r y).IsChain UnitStep := by
  constructor
  · apply List.Nodup.map _ List.nodup_range
    intro k l h
    have hh := pathPoint_injective span height r h
    omega
  · rw [tailPath,List.isChain_map,List.isChain_range]
    intro k hk
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      pathPoint_step span height r (k+cut span height r y)

theorem headPath_endpoints (span height : Nat) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    (headPath span height r y).head?=some (0,(height:Int)+offset r) ∧
    (headPath span height r y).getLast?=some ((turn span r:Int),y) := by
  constructor
  · simp [headPath,List.range_succ_eq_map,pathPoint]
  · simp [headPath,List.range_succ,cut_point span height r y hy]

theorem tailPath_endpoints (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    (tailPath span height tail r y).head?=some ((turn span r:Int),y) ∧
    (tailPath span height tail r y).getLast?=some ((finish span tail:Int),offset r) := by
  have hc := cut_bounds span height r y hy
  have ht := turn_bounds span tail hs r
  constructor
  · simp [tailPath,List.range_succ_eq_map,cut_point span height r y hy]
  · have he : finish span tail+height-cut span height r y+cut span height r y=
        finish span tail+height := by omega
    simp only [tailPath,List.range_succ,List.map_append,List.map_cons,List.map_nil,
      List.getLast?_append,List.getLast?_singleton,he]
    simp only [pathPoint,ite_eq_right (show ¬finish span tail+height≤turn span r by omega),
      ite_eq_right (show ¬finish span tail+height≤turn span r+height by omega)]
    simp

theorem headPath_subset (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    headPath span height r y ⊆ path span height tail r := by
  have hc := cut_bounds span height r y hy
  have ht := turn_bounds span tail hs r
  intro q hq
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨k,by simp only [List.mem_range] at hk ⊢; omega,rfl⟩

theorem tailPath_subset (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) :
    tailPath span height tail r y ⊆ path span height tail r := by
  have hc := cut_bounds span height r y hy
  have ht := turn_bounds span tail hs r
  intro q hq
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨k+cut span height r y,by simp only [List.mem_range] at hk ⊢; omega,rfl⟩

theorem headPath_mem (span height : Nat) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) (q : Point) :
    q∈headPath span height r y ↔
      (q.2=(height:Int)+offset r ∧ 0≤q.1 ∧ q.1≤turn span r) ∨
      (q.1=(turn span r:Int) ∧ y≤q.2 ∧ q.2≤(height:Int)+offset r) := by
  have hc := cut_bounds span height r y hy
  constructor
  · intro hq
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range] at hk
    dsimp [pathPoint]
    split_ifs
    · exact Or.inl ⟨rfl,by omega,by omega⟩
    · exact Or.inr ⟨rfl,by omega,by omega⟩
    · omega
  · intro hq
    apply List.mem_map.mpr
    rcases hq with ⟨he,hl,hu⟩ | ⟨he,hl,hu⟩
    · refine ⟨q.1.toNat,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega
    · let k := ((turn span r:Int)+height+offset r-q.2).toNat
      have hk : (k:Int)=(turn span r:Int)+height+offset r-q.2 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega

theorem tailPath_mem (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (y : Int)
    (hy : offset r ≤y ∧ y ≤(height :Int) +offset r) (q : Point) :
    q∈tailPath span height tail r y ↔
      (q.1=(turn span r:Int) ∧ offset r≤q.2 ∧ q.2≤y) ∨
      (q.2=offset r ∧ (turn span r:Int)≤q.1 ∧ q.1≤finish span tail) := by
  have hc := cut_bounds span height r y hy
  have ht := turn_bounds span tail hs r
  constructor
  · intro hq
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range] at hk
    dsimp [pathPoint]
    split_ifs
    · exact Or.inl ⟨by omega,by omega,by omega⟩
    · exact Or.inl ⟨rfl,by omega,by omega⟩
    · exact Or.inr ⟨rfl,by omega,by omega⟩
  · intro hq
    apply List.mem_map.mpr
    rcases hq with ⟨he,hl,hu⟩ | ⟨he,hl,hu⟩
    · let k := (y-q.2).toNat
      have hk : (k:Int)=y-q.2 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega
    · let k := (q.1+height-cut span height r y).toNat
      have hk : (k:Int)=q.1+height-cut span height r y := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega

variable {n : Nat} (p : Equiv.Perm (Fin n))

def FirstInColumn (i j : Fin n) : Prop :=
  SatCrossingRouting.Active p i j ∧ ∀ k, SatCrossingRouting.Active p i k → p j≤p k

def LastInColumn (i j : Fin n) : Prop :=
  SatCrossingRouting.Active p i j ∧ ∀ k, SatCrossingRouting.Active p i k → p k≤p j

/-- Local height of the upper or lower boundary of a future crossing. -/
def cutHeight (i j : Fin n) (upper : Bool) : Int :=
  512*(high p j-low i)+(if upper then 10 else -10)

/-- False-side residual edge, directed consistently with the mandatory arc. -/
def upper (last : Option (Fin n)) (i j : Fin n) (r : Fin 4) : List Point :=
  let l := (headPath (Placement.span last i) (Placement.height p i) r
    (cutHeight p i j true)).map (Placement.frame last i).map
  if r.val%2=0 then l else l.reverse

/-- Variable-side residual edge, directed consistently with the mandatory arc. -/
def lower (last : Option (Fin n)) (i j : Fin n) (r : Fin 4) : List Point :=
  let l := (tailPath (Placement.span last i) (Placement.height p i) (Placement.tail i) r
    (cutHeight p i j false)).map (Placement.frame last i).map
  if r.val%2=0 then l else l.reverse

theorem cutHeight_bounds (i j : Fin n) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (b : Bool) :
    offset r≤cutHeight p i j b ∧
    cutHeight p i j b≤(Placement.height p i:Int)+offset r := by
  have hi := low_bounds i
  have hj := high_bounds p j
  have hh := (high_lt_high p).mpr hij.2
  have ho := offset_bounds r
  dsimp [cutHeight,Placement.height]
  split_ifs <;> omega

private theorem orient_simple (l : List Point) (r : Fin 4)
    (h : l.Nodup ∧ l.IsChain UnitStep) :
    (if r.val%2=0 then l else l.reverse).Nodup ∧
    (if r.val%2=0 then l else l.reverse).IsChain UnitStep := by
  split_ifs
  · exact h
  · refine ⟨List.nodup_reverse.mpr h.1,List.isChain_reverse.mpr (h.2.imp ?_)⟩
    intro a b hab
    change IntegerGrid.manhattan _ _=1 at hab ⊢
    dsimp [IntegerGrid.manhattan] at hab ⊢
    omega

private theorem map_simple (last : Option (Fin n)) (i : Fin n) (l : List Point)
    (h : l.Nodup ∧ l.IsChain UnitStep) :
    (l.map (Placement.frame last i).map).Nodup ∧
    (l.map (Placement.frame last i).map).IsChain UnitStep := by
  refine ⟨h.1.map (Placement.frame last i).injective,?_⟩
  apply List.isChain_map_of_isChain _ _ h.2
  intro a b hab
  change IntegerGrid.manhattan _ _=1
  rw [(Placement.frame last i).distance]
  exact hab

theorem upper_simple (last : Option (Fin n)) (i j : Fin n) (r : Fin 4) :
    (upper p last i j r).Nodup ∧ (upper p last i j r).IsChain UnitStep :=
  orient_simple _ r (map_simple last i _ (headPath_simple _ _ _ _))

theorem lower_simple (last : Option (Fin n)) (i j : Fin n) (r : Fin 4) :
    (lower p last i j r).Nodup ∧ (lower p last i j r).IsChain UnitStep :=
  orient_simple _ r (map_simple last i _ (tailPath_simple _ _ _ _ _))

theorem upper_subset (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    upper p last i j r ⊆ Placement.route p last i r := by
  intro q hq
  have hp := Placement.parameters p last i hl
  simp only [upper] at hq
  split_ifs at hq
  all_goals try simp only [List.mem_reverse] at hq
  all_goals
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
    apply List.mem_map.mpr
    refine ⟨t,?_,rfl⟩
    rw [SatCrossingRetirement.route_mem]
    exact headPath_subset _ _ _ hp.2.1 r _ (cutHeight_bounds p i j hij r true) ht

theorem lower_subset (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    lower p last i j r ⊆ Placement.route p last i r := by
  intro q hq
  have hp := Placement.parameters p last i hl
  simp only [lower] at hq
  split_ifs at hq
  all_goals try simp only [List.mem_reverse] at hq
  all_goals
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
    apply List.mem_map.mpr
    refine ⟨t,?_,rfl⟩
    rw [SatCrossingRetirement.route_mem]
    exact tailPath_subset _ _ _ hp.2.1 r _ (cutHeight_bounds p i j hij r false) ht

theorem upper_coordinates_bounded (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (q : Point) (hq : q ∈upper p last i j r) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 :=
  Placement.coordinates_bounded p last i hl r q (upper_subset p last i j hl hij r hq)

theorem lower_coordinates_bounded (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (q : Point) (hq : q ∈lower p last i j r) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 :=
  Placement.coordinates_bounded p last i hl r q (lower_subset p last i j hl hij r hq)

theorem upper_mem (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (q : Point) :
    q∈upper p last i j r ↔
      (q.2=512*high p i+offset r ∧ Placement.left last≤q.1 ∧ q.1≤SatCrossingRouting.lane i r) ∨
      (q.1=SatCrossingRouting.lane i r ∧ 512*high p j+10≤q.2 ∧ q.2≤512*high p i+offset r) := by
  have hp := Placement.parameters p last i hl
  have ht := turn_cast (Placement.span last i) hp.2.1 r
  have hc := cutHeight_bounds p i j hij r true
  have hm : ∀ t : Point, t∈headPath (Placement.span last i) (Placement.height p i) r
      (cutHeight p i j true) ↔
      (t.2=(Placement.height p i:Int)+offset r ∧ 0≤t.1 ∧ t.1≤turn (Placement.span last i) r) ∨
      (t.1=(turn (Placement.span last i) r:Int) ∧ cutHeight p i j true≤t.2 ∧
        t.2≤(Placement.height p i:Int)+offset r) := headPath_mem _ _ _ _ hc
  have hmap : q∈(headPath (Placement.span last i) (Placement.height p i) r
      (cutHeight p i j true)).map (Placement.frame last i).map ↔
      (q.2=512*high p i+offset r ∧ Placement.left last≤q.1 ∧ q.1≤SatCrossingRouting.lane i r) ∨
      (q.1=SatCrossingRouting.lane i r ∧ 512*high p j+10≤q.2 ∧ q.2≤512*high p i+offset r) := by
    constructor
    · intro hq
      obtain ⟨t,htq,rfl⟩ := List.mem_map.mp hq
      rw [Placement.frame_map]
      have hh := (hm t).mp htq
      dsimp [SatCrossingRouting.lane,cutHeight] at hh ⊢
      rcases hh with hh | hh
      · exact Or.inl ⟨by omega,by omega,by omega⟩
      · exact Or.inr ⟨by omega,by omega,by omega⟩
    · intro hq
      apply List.mem_map.mpr
      refine ⟨(q.1-Placement.left last,q.2-512*low i),?_,?_⟩
      · rw [hm]
        dsimp [SatCrossingRouting.lane,cutHeight] at hq ⊢
        rcases hq with hq | hq
        · exact Or.inl ⟨by omega,by omega,by omega⟩
        · exact Or.inr ⟨by omega,by omega,by omega⟩
      · rw [Placement.frame_map]
        apply Prod.ext <;> dsimp <;> omega
  unfold upper
  split_ifs <;> simpa only [List.mem_reverse] using hmap

theorem lower_mem (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (q : Point) :
    q∈lower p last i j r ↔
      (q.1=SatCrossingRouting.lane i r ∧ 512*low i+offset r≤q.2 ∧ q.2≤512*high p j-10) ∨
      (q.2=512*low i+offset r ∧ SatCrossingRouting.lane i r≤q.1 ∧ q.1≤512*((n:Int)+1)+65) := by
  have hp := Placement.parameters p last i hl
  have ht := turn_cast (Placement.span last i) hp.2.1 r
  have hc := cutHeight_bounds p i j hij r false
  have hm := tailPath_mem (Placement.span last i) (Placement.height p i) (Placement.tail i)
    hp.2.1 r (cutHeight p i j false) hc
  have hmap : q∈(tailPath (Placement.span last i) (Placement.height p i) (Placement.tail i) r
      (cutHeight p i j false)).map (Placement.frame last i).map ↔
      (q.1=SatCrossingRouting.lane i r ∧ 512*low i+offset r≤q.2 ∧ q.2≤512*high p j-10) ∨
      (q.2=512*low i+offset r ∧ SatCrossingRouting.lane i r≤q.1 ∧ q.1≤512*((n:Int)+1)+65) := by
    constructor
    · intro hq
      obtain ⟨t,htq,rfl⟩ := List.mem_map.mp hq
      rw [Placement.frame_map]
      have hh := (hm t).mp htq
      dsimp [SatCrossingRouting.lane,cutHeight,finish] at hh ⊢
      rcases hh with hh | hh
      · exact Or.inl ⟨by omega,by omega,by omega⟩
      · exact Or.inr ⟨by omega,by omega,by omega⟩
    · intro hq
      apply List.mem_map.mpr
      refine ⟨(q.1-Placement.left last,q.2-512*low i),?_,?_⟩
      · rw [hm]
        dsimp [SatCrossingRouting.lane,cutHeight,finish] at hq ⊢
        rcases hq with hq | hq
        · exact Or.inl ⟨by omega,by omega,by omega⟩
        · exact Or.inr ⟨by omega,by omega,by omega⟩
      · rw [Placement.frame_map]
        apply Prod.ext <;> dsimp <;> omega
  unfold lower
  split_ifs <;> simpa only [List.mem_reverse] using hmap

theorem upper_endpoints (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    (upper p last i j r).head?=some
      (if r.val%2=0 then Placement.point p last i (falseVertex r)
       else point p (i,j) (XorLine.outputPort 4 (.inr r))) ∧
    (upper p last i j r).getLast?=some
      (if r.val%2=0 then point p (i,j) (XorLine.inputPort 4 (.inr r))
       else Placement.point p last i (falseVertex r)) := by
  have hp := Placement.parameters p last i hl
  have ht := turn_cast (Placement.span last i) hp.2.1 r
  have he := headPath_endpoints (Placement.span last i) (Placement.height p i) r
    (cutHeight p i j true) (cutHeight_bounds p i j hij r true)
  have hc := SatCrossingRouting.row_port_coordinates p (i,j) r
  rw [Placement.false_coordinates p last i hl r]
  unfold upper
  split_ifs with hr
  all_goals
    simp only [List.head?_reverse,List.getLast?_reverse,List.head?_map,List.getLast?_map,
      he.1,he.2,Option.map_some,Placement.frame_map,hc.1,hc.2,hr,ite_true,ite_false]
    constructor <;> congr 1 <;> apply Prod.ext <;> dsimp [cutHeight,SatCrossingRouting.lane] <;> omega

theorem lower_endpoints (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    (lower p last i j r).head?=some
      (if r.val%2=0 then point p (i,j) (XorLine.outputPort 4 (.inr r))
       else Placement.point p last i (trueVertex r)) ∧
    (lower p last i j r).getLast?=some
      (if r.val%2=0 then Placement.point p last i (trueVertex r)
       else point p (i,j) (XorLine.inputPort 4 (.inr r))) := by
  have hp := Placement.parameters p last i hl
  have ht := turn_cast (Placement.span last i) hp.2.1 r
  have he := tailPath_endpoints (Placement.span last i) (Placement.height p i) (Placement.tail i)
    hp.2.1 r (cutHeight p i j false) (cutHeight_bounds p i j hij r false)
  have hc := SatCrossingRouting.row_port_coordinates p (i,j) r
  rw [Placement.true_coordinates p last i hl r]
  unfold lower
  split_ifs with hr
  all_goals
    simp only [List.head?_reverse,List.getLast?_reverse,List.head?_map,List.getLast?_map,
      he.1,he.2,Option.map_some,Placement.frame_map,hc.1,hc.2,hr,ite_true,ite_false]
    constructor <;> congr 1 <;> apply Prod.ext <;> dsimp [cutHeight,SatCrossingRouting.lane,finish] <;> omega

/-- The last horizontal crossing, including the empty row case. -/
def LastInRow (last : Option (Fin n)) (i : Fin n) : Prop :=
  match last with
  | none => ∀ a, ¬SatCrossingRouting.Active p a i
  | some k => SatCrossingRouting.Active p k i ∧ ∀ a, SatCrossingRouting.Active p a i → a≤k

theorem lastInRow_before (last : Option (Fin n)) (i : Fin n)
    (hl : LastInRow p last i) : Placement.LastBefore last i := by
  intro k hk
  subst last
  exact hl.1.1

/-- Every point of a lower tail in an active crossing box is its designated
lower row port. This includes all columns, not just the retired wire's column. -/
theorem lower_box_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hj : FirstInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (q : Point) (hq : q ∈lower p last i j r) (hb : InBox p d q) :
    d=(i,j) ∧ q=(SatCrossingRouting.lane i r,512*high p j-10) := by
  have hm := (lower_mem p last i j hl hj.1 r q).mp hq
  have hi := low_bounds i
  have hd' := high_bounds p d.2
  have ho := offset_bounds r
  have hr := r.isLt
  dsimp [InBox] at hb
  rcases hm with ⟨hx,hy,hz⟩ | ⟨hy,hx,hz⟩
  · have hdi : d.1=i := by
      apply low_injective
      dsimp [SatCrossingRouting.lane] at hx
      omega
    have hdj : d.2=j := by
      have he := hj.2 d.2 (by simpa [hdi] using hd)
      have hhe : high p j≤high p d.2 := by dsimp [high]; omega
      apply high_injective p
      omega
    refine ⟨Prod.ext hdi hdj,Prod.ext hx ?_⟩
    dsimp
    subst hdj
    omega
  · omega

/-- The upper tail misses every unrelated active box. The last horizontal
box is excluded here because its section-zero vertices are retired in place;
`upper_latest_retained_clear` handles its forty surviving vertices. -/
theorem upper_other_box_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : LastInRow p last i) (hj : LastInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (hdj : d ≠(i, j)) (hprev : last ≠some d.1 ∨ d.2 ≠i)
    (q : Point) (hq : q ∈upper p last i j r) : ¬InBox p d q := by
  intro hb
  have hm := (upper_mem p last i j (lastInRow_before p last i hl) hj.1 r q).mp hq
  have ho := offset_bounds r
  have hr := r.isLt
  dsimp [InBox] at hb
  rcases hm with ⟨hy,hx,hz⟩ | ⟨hx,hy,hz⟩
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
    have hd' : SatCrossingRouting.Active p i d.2 := by simpa [hdi] using hd
    have hle := hj.2 d.2 hd'
    have hh : high p d.2≤high p j := by dsimp [high]; omega
    have hde : d.2=j := high_injective p (by omega)
    exact hdj (Prod.ext hdi hde)

theorem upper_endpoint_box (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j)
    (r : Fin 4) (q : Point) (hq : q ∈upper p last i j r) :
    InBox p (i,j) q ↔ q=(SatCrossingRouting.lane i r,512*high p j+10) := by
  have hm := (upper_mem p last i j hl hij r q).mp hq
  have hh := (high_lt_high p).mpr hij.2
  have ho := offset_bounds r
  have hr := r.isLt
  constructor
  · intro hb
    dsimp [InBox] at hb
    rcases hm with ⟨hy,hx,hz⟩ | ⟨hx,hy,hz⟩
    · omega
    · exact Prod.ext hx (by dsimp; omega)
  · rintro rfl
    dsimp [InBox,SatCrossingRouting.lane]
    omega

theorem upper_latest_retained_clear (a i j : Fin n) (hai : a < i)
    (hij : SatCrossingRouting.Active p i j) (r : Fin 4)
    (v : SatCrossingHorizontal.RetainedVertex) :
    point p (a,i) v.val ∉ upper p (some a) i j r := by
  intro hq
  have hm := (upper_mem p (some a) i j (by intro k hk; cases hk; exact hai) hij r _).mp hq
  have hb := SatCrossingHorizontal.retained_bound p (a,i) v
  dsimp only [Prod.fst] at hb
  have hh := low_lt_low hai
  have hr := r.isLt
  dsimp [Placement.left,SatCrossingRouting.lane] at hm
  rcases hm with hm | hm <;> omega

/-- The lower tail meets exactly one vertex of any active crossing, namely
the appropriate lower-side row port of the first cell. -/
theorem lower_vertex_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hj : FirstInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (v : XorLine.Vertex 4) :
    point p d v∈lower p last i j r ↔
      d=(i,j) ∧ v=SatCrossingRouting.upperPort r := by
  constructor
  · intro hv
    obtain ⟨hd',he⟩ := lower_box_clear p last i j hl hj r d hd _ hv (point_in_box p d v)
    subst d
    refine ⟨rfl,?_⟩
    rw [← SatCrossingRouting.upperPort_coordinates p i j r] at he
    exact congrArg Prod.snd (@SatCrossingLattice.point_injective n p
      ((i,j),v) ((i,j),SatCrossingRouting.upperPort r) he)
  · rintro ⟨rfl,rfl⟩
    rw [SatCrossingRouting.upperPort_coordinates,lower_mem p last i j hl hj.1]
    left
    have hi := low_bounds i
    have hh := high_bounds p j
    have ho := offset_bounds r
    exact ⟨rfl,by omega,by omega⟩

/-- Among all retained crossing vertices, an upper tail meets only its own
upper-side row endpoint. Retired section zero is not counted a second time. -/
theorem upper_retained_vertex_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : LastInRow p last i) (hj : LastInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (v : SatCrossingHorizontal.RetainedVertex) :
    point p d v.val∈upper p last i j r ↔
      d=(i,j) ∧ v.val=SatCrossingRouting.lowerPort r := by
  have hl' := lastInRow_before p last i hl
  constructor
  · intro hv
    by_cases hdj : d=(i,j)
    · subst d
      have he := (upper_endpoint_box p last i j hl' hj.1 r _ hv).mp (point_in_box p _ _)
      rw [← SatCrossingRouting.lowerPort_coordinates p i j r] at he
      exact ⟨rfl,congrArg Prod.snd (@SatCrossingLattice.point_injective n p
        ((i,j),v.val) ((i,j),SatCrossingRouting.lowerPort r) he)⟩
    · by_cases hh : last=some d.1 ∧ d.2=i
      · obtain ⟨hh,hi⟩ := hh
        have hdi := hl' d.1 hh
        change point p (d.1,d.2) v.val∈upper p last i j r at hv
        rw [hh,hi] at hv
        exact False.elim (upper_latest_retained_clear p d.1 i j hdi hj.1 r v hv)
      · have hh' : last≠some d.1 ∨ d.2≠i := by tauto
        exact False.elim (upper_other_box_clear p last i j hl hj r d hd hdj hh' _ hv
          (point_in_box p d v.val))
  · rintro ⟨rfl,hv⟩
    rw [hv,SatCrossingRouting.lowerPort_coordinates,upper_mem p last i j hl' hj.1]
    right
    have hh := (high_lt_high p).mpr hj.1.2
    have ho := offset_bounds r
    exact ⟨rfl,le_rfl,by omega⟩

theorem upper_length_bound (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    (upper p last i j r).length≤2048*(n+1) :=
  le_trans ((upper_simple p last i j r).1.length_le_of_subset (upper_subset p last i j hl hij r))
    (Placement.route_length_bound p last i hl r)

theorem lower_length_bound (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hij : SatCrossingRouting.Active p i j) (r : Fin 4) :
    (lower p last i j r).length≤2048*(n+1) :=
  le_trans ((lower_simple p last i j r).1.length_le_of_subset (lower_subset p last i j hl hij r))
    (Placement.route_length_bound p last i hl r)

theorem upper_lower_disjoint (last : Option (Fin n)) (i j k : Fin n)
    (hl : Placement.LastBefore last i) (hj : FirstInColumn p i j) (hk : LastInColumn p i k)
    (r s : Fin 4) : (upper p last i k r).Disjoint (lower p last i j s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hu := (upper_mem p last i k hl hk.1 r q).mp hq
  have hd := (lower_mem p last i j hl hj.1 s q).mp ht
  have hh := hj.2 k hk.1
  have hle : high p j≤high p k := by dsimp [high]; omega
  have hi := low_bounds i
  have hb := high_bounds p k
  have hic := (high_lt_high p).mpr hk.1.2
  have hor := offset_bounds r
  have hos := offset_bounds s
  rcases hu with hu | hu <;> rcases hd with hd | hd <;> omega

theorem upper_distinct_rows (last : Option (Fin n)) (i j k : Fin n)
    (hl : Placement.LastBefore last i) (hj : SatCrossingRouting.Active p i j)
    (hk : SatCrossingRouting.Active p i k) (r s : Fin 4) (hrs : r ≠s) :
    (upper p last i j r).Disjoint (upper p last i k s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  exact List.disjoint_left.mp (Placement.routes_disjoint p last i hl r s hrs)
    (upper_subset p last i j hl hj r hq) (upper_subset p last i k hl hk s ht)

theorem lower_distinct_rows (last : Option (Fin n)) (i j k : Fin n)
    (hl : Placement.LastBefore last i) (hj : SatCrossingRouting.Active p i j)
    (hk : SatCrossingRouting.Active p i k) (r s : Fin 4) (hrs : r ≠s) :
    (lower p last i j r).Disjoint (lower p last i k s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  exact List.disjoint_left.mp (Placement.routes_disjoint p last i hl r s hrs)
    (lower_subset p last i j hl hj r hq) (lower_subset p last i k hl hk s ht)

end GridHardness.SatCrossingRetirement.Segments
