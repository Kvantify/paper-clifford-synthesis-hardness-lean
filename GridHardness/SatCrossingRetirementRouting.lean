/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRouting
public import GridHardness.XorLineMarked

/-!
# SAT Crossing Retirement Routing

A two-bend drawing of the four mandatory arcs of a retired XOR.
Its false-side vertices remain by the last crossing; its true-side vertices
move to the variable boundary. Thus retirement changes the placement of the
active eight-vertex XOR, rather than retaining its compact section-zero
coordinates. The transverse lanes agree with the crossing-cell row order.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement
open CliffordSynthesis XorLine
set_option autoImplicit false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

/-- Vertical offsets of the four vertices in either endpoint column. -/
def offset : Fin 4 → Int := ![4,2,-2,-4]

/-- The vertical lane of row `r`, relative to the false endpoint column. -/
def turn (span : Nat) (r : Fin 4) : Nat := span+45-30*r.val

/-- Horizontal position of the true endpoint column. -/
def finish (span tail : Nat) : Nat := span+46+tail

def pathPoint (span height : Nat) (r : Fin 4) (k : Nat) : Point :=
  if k≤turn span r then ((k:Int),(height:Int)+offset r)
  else if k≤turn span r+height then
    ((turn span r:Int),(height:Int)+offset r-((k:Int)-turn span r))
  else ((k:Int)-height,offset r)

def path (span height tail : Nat) (r : Fin 4) : List Point :=
  (List.range (finish span tail+height+1)).map (pathPoint span height r)

/-- Even rows point from the false column to the true column; odd rows have
exactly the opposite direction, as prescribed by the actual XOR arcs. -/
def route (span height tail : Nat) (r : Fin 4) : List Point :=
  if r.val%2=0 then path span height tail r else (path span height tail r).reverse

theorem offset_bounds : ∀ r : Fin 4, -4≤offset r ∧ offset r≤4 := by decide

theorem offset_strict : ∀ r s : Fin 4, r<s → offset s<offset r := by decide

theorem turn_cast (span : Nat) (hs : 46 ≤span) (r : Fin 4) :
    (turn span r:Int)=(span:Int)+45-30*r.val := by
  have hr := r.isLt
  dsimp [turn]
  omega

theorem turn_bounds (span tail : Nat) (hs : 46 ≤span) (r : Fin 4) :
    0<turn span r ∧ turn span r<finish span tail := by
  have hr := r.isLt
  have hc := turn_cast span hs r
  dsimp [finish]
  omega

theorem turn_strict (span : Nat) (hs : 46 ≤span) (r s : Fin 4) (hrs : r <s) :
    turn span s<turn span r := by
  have hr := turn_cast span hs r
  have hss := turn_cast span hs s
  omega

theorem pathPoint_injective (span height : Nat) (r : Fin 4) :
    Function.Injective (pathPoint span height r) := by
  intro k l he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [pathPoint] at hx hy
  split_ifs at hx hy <;> omega

theorem path_nodup (span height tail : Nat) (r : Fin 4) :
    (path span height tail r).Nodup :=
  List.Nodup.map (pathPoint_injective span height r) List.nodup_range

theorem path_chain (span height tail : Nat) (r : Fin 4) :
    (path span height tail r).IsChain UnitStep := by
  rw [path,List.isChain_map,List.isChain_range]
  intro k hk
  change IntegerGrid.manhattan (pathPoint span height r k)
    (pathPoint span height r (k+1))=1
  dsimp [pathPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem path_head (span height tail : Nat) (r : Fin 4) :
    (path span height tail r).head?=some (0,(height:Int)+offset r) := by
  simp [path,List.range_succ_eq_map,pathPoint]

theorem path_last (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) :
    (path span height tail r).getLast?=some ((finish span tail:Int),offset r) := by
  have ht := (turn_bounds span tail hs r).2
  simp only [path,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    List.getLast?_append,List.getLast?_singleton]
  simp only [pathPoint,ite_eq_right (show ¬finish span tail+height≤turn span r from by omega),
    ite_eq_right (show ¬finish span tail+height≤turn span r+height from by omega)]
  simp

theorem path_length (span height tail : Nat) (r : Fin 4) :
    (path span height tail r).length=span+height+tail+47 := by
  simp [path,finish]
  omega

/-- Exact closed-segment membership of the explicit list. -/
theorem path_mem (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (q : Point) :
    q ∈ path span height tail r ↔
      (q.2=(height:Int)+offset r ∧ 0≤q.1 ∧ q.1≤turn span r) ∨
      (q.1=(turn span r:Int) ∧ offset r≤q.2 ∧ q.2≤(height:Int)+offset r) ∨
      (q.2=offset r ∧ (turn span r:Int)≤q.1 ∧ q.1≤finish span tail) := by
  have ht := turn_bounds span tail hs r
  constructor
  · intro hq
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range] at hk
    dsimp [pathPoint]
    split_ifs
    · exact Or.inl ⟨rfl,by omega,by omega⟩
    · exact Or.inr (Or.inl ⟨rfl,by omega,by omega⟩)
    · exact Or.inr (Or.inr ⟨rfl,by omega,by omega⟩)
  · intro hq
    apply List.mem_map.mpr
    rcases hq with ⟨hy,hl,hu⟩ | ⟨hx,hl,hu⟩ | ⟨hy,hl,hu⟩
    · refine ⟨q.1.toNat,by simp only [List.mem_range]; omega,?_⟩
      simp only [pathPoint,ite_eq_left (show q.1.toNat≤turn span r from by omega)]
      apply Prod.ext <;> dsimp <;> omega
    · let k : Nat := ((turn span r:Int)+height+offset r-q.2).toNat
      have hk : (k:Int)=(turn span r:Int)+height+offset r-q.2 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega
    · let k : Nat := (q.1+height).toNat
      have hk : (k:Int)=q.1+height := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [pathPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega

theorem paths_disjoint (span height tail : Nat) (hs : 46 ≤span) (hh : 9 ≤height)
    (r s : Fin 4) (hrs : r ≠s) : (path span height tail r).Disjoint (path span height tail s) := by
  apply List.disjoint_left.mpr
  intro q hqr hqs
  have hr := (path_mem span height tail hs r q).mp hqr
  have hss := (path_mem span height tail hs s q).mp hqs
  have hor := offset_bounds r
  have hos := offset_bounds s
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · have ho := offset_strict r s hlt
    have ht := turn_strict span hs r s hlt
    rcases hr with hr | hr | hr <;> rcases hss with hss | hss | hss <;> omega
  · have ho := offset_strict s r hgt
    have ht := turn_strict span hs s r hgt
    rcases hr with hr | hr | hr <;> rcases hss with hss | hss | hss <;> omega

theorem route_mem (span height tail : Nat) (r : Fin 4) (q : Point) :
    q ∈ route span height tail r ↔ q ∈ path span height tail r := by
  unfold route
  split_ifs <;> simp

theorem route_simple (span height tail : Nat) (r : Fin 4) :
    (route span height tail r).Nodup ∧ (route span height tail r).IsChain UnitStep := by
  unfold route
  split_ifs
  · exact ⟨path_nodup _ _ _ _,path_chain _ _ _ _⟩
  · refine ⟨List.nodup_reverse.mpr (path_nodup _ _ _ _),?_⟩
    apply List.isChain_reverse.mpr
    apply (path_chain span height tail r).imp
    intro q t h
    change IntegerGrid.manhattan _ _=1 at h ⊢
    dsimp [IntegerGrid.manhattan] at h ⊢
    omega

theorem routes_disjoint (span height tail : Nat) (hs : 46 ≤span) (hh : 9 ≤height)
    (r s : Fin 4) (hrs : r ≠s) : (route span height tail r).Disjoint (route span height tail s) := by
  apply List.disjoint_left.mpr
  intro q hqr hqs
  exact List.disjoint_left.mp (paths_disjoint span height tail hs hh r s hrs)
    ((route_mem span height tail r q).mp hqr) ((route_mem span height tail s q).mp hqs)

theorem route_length (span height tail : Nat) (r : Fin 4) :
    (route span height tail r).length=span+height+tail+47 := by
  unfold route
  split_ifs <;> simp [path_length]

theorem route_bounds (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (q : Point)
    (hq : q ∈ route span height tail r) :
    0≤q.1 ∧ q.1≤finish span tail ∧ -4≤q.2 ∧ q.2≤(height:Int)+4 := by
  have hm := (path_mem span height tail hs r q).mp ((route_mem span height tail r q).mp hq)
  have ho := offset_bounds r
  have ht := turn_bounds span tail hs r
  rcases hm with hm | hm | hm <;> omega

/-- Indices of the true and false endpoint vertices of a retired XOR. -/
def trueVertex (r : Fin 4) : Fin 8 := ⟨r.val,by omega⟩
def falseVertex (r : Fin 4) : Fin 8 := ⟨r.val+4,by omega⟩

theorem vertex_split : ∀ v : Fin 8, ∃ r : Fin 4, v=trueVertex r ∨ v=falseVertex r := by decide

theorem crossArc_endpoints : ∀ r : Fin 4,
    (XorGadget.arc (Marked.crossArc r)).1=(if r.val%2=0 then falseVertex r else trueVertex r) ∧
    (XorGadget.arc (Marked.crossArc r)).2=(if r.val%2=0 then trueVertex r else falseVertex r) := by decide

/-- Split the actual eight XOR vertices between the two endpoint columns.
Only the true-side column moves to the variable boundary. -/
def vertexPoint (span height tail : Nat) (v : Fin 8) : Point :=
  if v.val<4 then ((finish span tail:Int),offset ⟨v.val%4,Nat.mod_lt _ (by decide)⟩)
  else (0,(height:Int)+offset ⟨v.val%4,Nat.mod_lt _ (by decide)⟩)

theorem trueVertex_coordinates (span height tail : Nat) (r : Fin 4) :
    vertexPoint span height tail (trueVertex r)=((finish span tail:Int),offset r) := by
  have hr := r.isLt
  simp [vertexPoint,trueVertex,Nat.mod_eq_of_lt hr,hr]

theorem falseVertex_coordinates (span height tail : Nat) (r : Fin 4) :
    vertexPoint span height tail (falseVertex r)=(0,(height:Int)+offset r) := by
  have hr := r.isLt
  simp [vertexPoint,falseVertex,show ¬r.val+4<4 by omega,Nat.mod_eq_of_lt hr]

theorem offset_injective : Function.Injective offset := by decide

theorem vertexPoint_injective (span height tail : Nat) :
    Function.Injective (vertexPoint span height tail) := by
  intro u v h
  obtain ⟨r,hr⟩ := vertex_split u
  obtain ⟨s,hs⟩ := vertex_split v
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · rw [trueVertex_coordinates,trueVertex_coordinates] at h
    exact congrArg trueVertex (offset_injective (congrArg Prod.snd h))
  · rw [trueVertex_coordinates,falseVertex_coordinates] at h
    have hh := congrArg Prod.fst h
    dsimp [finish] at hh
    omega
  · rw [falseVertex_coordinates,trueVertex_coordinates] at h
    have hh := congrArg Prod.fst h
    dsimp [finish] at hh
    omega
  · rw [falseVertex_coordinates,falseVertex_coordinates] at h
    have hh : offset r=offset s := by have ht := congrArg Prod.snd h; dsimp at ht; omega
    exact congrArg falseVertex (offset_injective hh)

/-- Directed endpoints are exactly the source and target of each of the four
actual mandatory XOR arcs registered by retirement. -/
theorem route_endpoints (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) :
    (route span height tail r).head?=
      some (vertexPoint span height tail (XorGadget.arc (Marked.crossArc r)).1) ∧
    (route span height tail r).getLast?=
      some (vertexPoint span height tail (XorGadget.arc (Marked.crossArc r)).2) := by
  obtain ⟨ha,hb⟩ := crossArc_endpoints r
  rw [ha,hb]
  unfold route
  by_cases he : r.val%2=0
  · simp [he,path_head,path_last span height tail hs,trueVertex_coordinates,falseVertex_coordinates]
  · simp [he,List.head?_reverse,List.getLast?_reverse,path_head,
      path_last span height tail hs,trueVertex_coordinates,falseVertex_coordinates]

theorem trueVertex_mem (span height tail : Nat) (hs : 46 ≤span) (r s : Fin 4) :
    vertexPoint span height tail (trueVertex s) ∈ route span height tail r ↔ s=r := by
  rw [trueVertex_coordinates,route_mem,path_mem span height tail hs]
  have ht := turn_bounds span tail hs r
  constructor
  · intro hm
    rcases hm with hm | hm | hm
    · dsimp at hm
      omega
    · dsimp at hm
      omega
    · exact offset_injective hm.1
  · rintro rfl
    exact Or.inr (Or.inr ⟨rfl,by dsimp; omega,le_rfl⟩)

theorem falseVertex_mem (span height tail : Nat) (hs : 46 ≤span) (r s : Fin 4) :
    vertexPoint span height tail (falseVertex s) ∈ route span height tail r ↔ s=r := by
  rw [falseVertex_coordinates,route_mem,path_mem span height tail hs]
  have ht := turn_bounds span tail hs r
  constructor
  · intro hm
    rcases hm with hm | hm | hm
    · have he : offset s=offset r := by dsimp at hm; omega
      exact offset_injective he
    · dsimp at hm
      omega
    · dsimp at hm
      omega
  · rintro rfl
    exact Or.inl ⟨rfl,le_rfl,by dsimp; omega⟩

/-- A mandatory route contains exactly its two XOR endpoint vertices. -/
theorem route_vertex_clear (span height tail : Nat) (hs : 46 ≤span) (r : Fin 4) (v : Fin 8) :
    vertexPoint span height tail v ∈ route span height tail r ↔
      v=(XorGadget.arc (Marked.crossArc r)).1 ∨ v=(XorGadget.arc (Marked.crossArc r)).2 := by
  have hm : vertexPoint span height tail v ∈ route span height tail r ↔
      v=trueVertex r ∨ v=falseVertex r := by
    obtain ⟨s,hv⟩ := vertex_split v
    rcases hv with rfl | rfl
    · rw [trueVertex_mem span height tail hs]
      constructor
      · rintro rfl; exact Or.inl rfl
      · rintro (he | he)
        · have hh := congrArg Fin.val he
          apply Fin.ext
          exact hh
        · have hh := congrArg Fin.val he
          have hr := s.isLt
          dsimp [trueVertex,falseVertex] at hh
          omega
    · rw [falseVertex_mem span height tail hs]
      constructor
      · rintro rfl; exact Or.inr rfl
      · rintro (he | he)
        · have hh := congrArg Fin.val he
          have hr := r.isLt
          dsimp [trueVertex,falseVertex] at hh
          omega
        · have hh := congrArg Fin.val he
          apply Fin.ext
          dsimp [falseVertex] at hh
          omega
  rw [hm,(crossArc_endpoints r).1,(crossArc_endpoints r).2]
  split_ifs <;> tauto

/-- The remaining six XOR arcs stay within the two endpoint columns. -/
def sideArc : Fin 6 → Fin 10 := ![0,2,3,6,7,9]
def sideTrue : Fin 6 → Bool := ![true,true,true,false,false,false]
def sideRows : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(2,1),(2,3),(1,0),(1,2),(3,2)]
def sidePoints : Fin 6 → List Int :=
  ![[4,3,2],[-2,-1,0,1,2],[-2,-3,-4],[2,3,4],[2,1,0,-1,-2],[-4,-3,-2]]

def sidePoint (span height tail : Nat) (e : Fin 6) (z : Int) : Point :=
  if sideTrue e then ((finish span tail:Int),z) else (0,(height:Int)+z)

def sideRoute (span height tail : Nat) (e : Fin 6) : List Point :=
  (sidePoints e).map (sidePoint span height tail e)

theorem all_arcs : ∀ a : Fin 10,
    (∃ r : Fin 4, Marked.crossArc r=a) ∨ (∃ e : Fin 6, sideArc e=a) := by decide

theorem sideArc_endpoints : ∀ e : Fin 6,
    (XorGadget.arc (sideArc e)).1=
      (if sideTrue e then trueVertex (sideRows e).1 else falseVertex (sideRows e).1) ∧
    (XorGadget.arc (sideArc e)).2=
      (if sideTrue e then trueVertex (sideRows e).2 else falseVertex (sideRows e).2) := by decide

private theorem sidePoints_certificate : ∀ e : Fin 6,
    (sidePoints e).head?=some (offset (sideRows e).1) ∧
    (sidePoints e).getLast?=some (offset (sideRows e).2) ∧
    (sidePoints e).Nodup ∧ (sidePoints e).IsChain (fun z w => (z-w).natAbs=1) ∧
    3≤(sidePoints e).length ∧ (sidePoints e).length≤5 ∧
    (∀ z∈sidePoints e, -4≤z ∧ z≤4) := by decide

private theorem sidePoints_vertex_clear : ∀ (e : Fin 6) (r : Fin 4),
    offset r∈sidePoints e ↔ r=(sideRows e).1 ∨ r=(sideRows e).2 := by decide

private theorem sidePoints_intersection : ∀ (e f : Fin 6), e≠f → sideTrue e=sideTrue f →
    ∀ z∈sidePoints e, z∈sidePoints f →
      (z=offset (sideRows e).1 ∨ z=offset (sideRows e).2) ∧
      (z=offset (sideRows f).1 ∨ z=offset (sideRows f).2) := by decide

theorem sidePoint_injective (span height tail : Nat) (e : Fin 6) :
    Function.Injective (sidePoint span height tail e) := by
  intro z w he
  have hh := congrArg Prod.snd he
  unfold sidePoint at hh
  split at hh <;> dsimp at hh <;> omega

theorem sidePoint_vertex (span height tail : Nat) (e : Fin 6) (r : Fin 4) :
    sidePoint span height tail e (offset r)=vertexPoint span height tail
      (if sideTrue e then trueVertex r else falseVertex r) := by
  unfold sidePoint
  split <;> simp [trueVertex_coordinates,falseVertex_coordinates]

theorem sideRoute_endpoints (span height tail : Nat) (e : Fin 6) :
    (sideRoute span height tail e).head?=some (vertexPoint span height tail (XorGadget.arc (sideArc e)).1) ∧
    (sideRoute span height tail e).getLast?=some (vertexPoint span height tail (XorGadget.arc (sideArc e)).2) := by
  have hc := sidePoints_certificate e
  simp only [sideRoute,List.head?_map,List.getLast?_map,hc.1,hc.2.1,Option.map_some,
    sidePoint_vertex,(sideArc_endpoints e).1,(sideArc_endpoints e).2]
  exact ⟨trivial,trivial⟩

theorem sideRoute_simple (span height tail : Nat) (e : Fin 6) :
    (sideRoute span height tail e).Nodup ∧ (sideRoute span height tail e).IsChain UnitStep ∧
    3≤(sideRoute span height tail e).length ∧ (sideRoute span height tail e).length≤5 := by
  have hc := sidePoints_certificate e
  refine ⟨hc.2.2.1.map (sidePoint_injective _ _ _ _),?_,?_,?_⟩
  · apply List.isChain_map_of_isChain (sidePoint span height tail e) _ hc.2.2.2.1
    intro z w h
    change IntegerGrid.manhattan _ _=1
    unfold sidePoint
    split <;> dsimp [IntegerGrid.manhattan] <;> omega
  · simpa [sideRoute] using hc.2.2.2.2.1
  · simpa [sideRoute] using hc.2.2.2.2.2.1

set_option maxHeartbeats 1600000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem sideRoute_vertex_clear (span height tail : Nat) (e : Fin 6) (v : Fin 8) :
    vertexPoint span height tail v ∈ sideRoute span height tail e ↔
      v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2 := by
  fin_cases e <;> fin_cases v <;>
    simp [sideRoute,sidePoints,sidePoint,sideTrue,vertexPoint,sideArc,XorGadget.arc,offset,finish] <;> omega

/-- A mandatory route and a column route meet only at a shared XOR vertex,
which is an endpoint of both corresponding directed edges. -/
theorem mandatory_side_intersection (span height tail : Nat) (hs : 46 ≤span)
    (r : Fin 4) (e : Fin 6) (q : Point)
    (hr : q ∈route span height tail r) (he : q ∈sideRoute span height tail e) :
    ∃ v : Fin 8, q=vertexPoint span height tail v ∧
      (v=(XorGadget.arc (Marked.crossArc r)).1 ∨ v=(XorGadget.arc (Marked.crossArc r)).2) ∧
      (v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2) := by
  obtain ⟨z,hz,hq⟩ := List.mem_map.mp he
  have hm := (path_mem span height tail hs r q).mp ((route_mem span height tail r q).mp hr)
  have ht := turn_bounds span tail hs r
  have hp : ∃ v : Fin 8, q=vertexPoint span height tail v := by
    unfold sidePoint at hq
    split at hq
    · refine ⟨trueVertex r,?_⟩
      rw [trueVertex_coordinates]
      rcases hm with hm | hm | hm
      · have hx := congrArg Prod.fst hq
        dsimp at hx
        omega
      · have hx := congrArg Prod.fst hq
        dsimp at hx
        omega
      · apply Prod.ext
        · exact (congrArg Prod.fst hq).symm
        · exact hm.1
    · refine ⟨falseVertex r,?_⟩
      rw [falseVertex_coordinates]
      rcases hm with hm | hm | hm
      · apply Prod.ext
        · exact (congrArg Prod.fst hq).symm
        · exact hm.1
      · have hx := congrArg Prod.fst hq
        dsimp at hx
        omega
      · have hx := congrArg Prod.fst hq
        dsimp at hx
        omega
  obtain ⟨v,hv⟩ := hp
  refine ⟨v,hv,?_,?_⟩
  · exact (route_vertex_clear span height tail hs r v).mp (hv ▸ hr)
  · exact (sideRoute_vertex_clear span height tail e v).mp (hv ▸ he)

/-- Distinct column routes also meet only at their common XOR endpoints. -/
theorem side_intersection (span height tail : Nat) (e f : Fin 6) (hef : e ≠f) (q : Point)
    (he : q ∈sideRoute span height tail e) (hf : q ∈sideRoute span height tail f) :
    ∃ v : Fin 8, q=vertexPoint span height tail v ∧
      (v=(XorGadget.arc (sideArc e)).1 ∨ v=(XorGadget.arc (sideArc e)).2) ∧
      (v=(XorGadget.arc (sideArc f)).1 ∨ v=(XorGadget.arc (sideArc f)).2) := by
  obtain ⟨z,hz,hzq⟩ := List.mem_map.mp he
  obtain ⟨w,hw,hwq⟩ := List.mem_map.mp hf
  have hxy := hzq.trans hwq.symm
  have hx := congrArg Prod.fst hxy
  have hb : sideTrue e=sideTrue f := by
    cases he' : sideTrue e <;> cases hf' : sideTrue f <;> try rfl
    all_goals simp [sidePoint,he',hf',finish] at hx
    all_goals omega
  have hzw : z=w := by
    have hy := congrArg Prod.snd hxy
    unfold sidePoint at hy
    rw [hb] at hy
    split_ifs at hy <;> dsimp at hy <;> omega
  subst w
  have hi := sidePoints_intersection e f hef hb z hz hw
  have hq : q=vertexPoint span height tail (XorGadget.arc (sideArc e)).1 ∨
      q=vertexPoint span height tail (XorGadget.arc (sideArc e)).2 := by
    rcases hi.1 with h | h
    · apply Or.inl
      rw [← hzq,h,sidePoint_vertex,(sideArc_endpoints e).1]
    · apply Or.inr
      rw [← hzq,h,sidePoint_vertex,(sideArc_endpoints e).2]
  obtain ⟨v,hv⟩ : ∃ v : Fin 8, q=vertexPoint span height tail v := by
    rcases hq with h | h
    · exact ⟨_,h⟩
    · exact ⟨_,h⟩
  refine ⟨v,hv,?_,?_⟩
  · exact (sideRoute_vertex_clear span height tail e v).mp (hv ▸ he)
  · exact (sideRoute_vertex_clear span height tail f v).mp (hv ▸ hf)

theorem sideRoute_bounds (span height tail : Nat) (e : Fin 6) (q : Point)
    (hq : q ∈sideRoute span height tail e) :
    0≤q.1 ∧ q.1≤finish span tail ∧ -4≤q.2 ∧ q.2≤(height:Int)+4 := by
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
  have hb := (sidePoints_certificate e).2.2.2.2.2.2 z hz
  unfold sidePoint
  split_ifs <;> dsimp <;> omega

/-- The four stretched arcs and six column arcs enumerate the whole XOR. -/
abbrev Edge := Fin 4 ⊕ Fin 6

def edgeArc : Edge → Fin 10
  | .inl r => Marked.crossArc r
  | .inr e => sideArc e

def edgeRoute (span height tail : Nat) : Edge → List Point
  | .inl r => route span height tail r
  | .inr e => sideRoute span height tail e

theorem edgeArc_bijective : Function.Bijective edgeArc := by decide

theorem edgeRoute_endpoints (span height tail : Nat) (hs : 46 ≤span) (e : Edge) :
    (edgeRoute span height tail e).head?=
      some (vertexPoint span height tail (XorGadget.arc (edgeArc e)).1) ∧
    (edgeRoute span height tail e).getLast?=
      some (vertexPoint span height tail (XorGadget.arc (edgeArc e)).2) := by
  cases e with
  | inl r => exact route_endpoints span height tail hs r
  | inr e => exact sideRoute_endpoints span height tail e

theorem edgeRoute_simple (span height tail : Nat) (e : Edge) :
    (edgeRoute span height tail e).Nodup ∧ (edgeRoute span height tail e).IsChain UnitStep := by
  cases e with
  | inl r => exact route_simple span height tail r
  | inr e => exact ⟨(sideRoute_simple span height tail e).1,(sideRoute_simple span height tail e).2.1⟩

theorem edgeRoute_vertex_clear (span height tail : Nat) (hs : 46 ≤span) (e : Edge) (v : Fin 8) :
    vertexPoint span height tail v∈edgeRoute span height tail e ↔
      v=(XorGadget.arc (edgeArc e)).1 ∨ v=(XorGadget.arc (edgeArc e)).2 := by
  cases e with
  | inl r => exact route_vertex_clear span height tail hs r v
  | inr e => exact sideRoute_vertex_clear span height tail e v

/-- All ten directed edges have nonintersecting interiors in the split-XOR
placement. Any intersection is a shared graph endpoint. -/
theorem edgeRoute_intersection (span height tail : Nat) (hs : 46 ≤span) (hh : 9 ≤height)
    (e f : Edge) (hef : e ≠f) (q : Point)
    (he : q ∈edgeRoute span height tail e) (hf : q ∈edgeRoute span height tail f) :
    ∃ v : Fin 8, q=vertexPoint span height tail v ∧
      (v=(XorGadget.arc (edgeArc e)).1 ∨ v=(XorGadget.arc (edgeArc e)).2) ∧
      (v=(XorGadget.arc (edgeArc f)).1 ∨ v=(XorGadget.arc (edgeArc f)).2) := by
  cases e with
  | inl r =>
    cases f with
    | inl s =>
      have hrs : r≠s := fun h => hef (congrArg Sum.inl h)
      exact False.elim (List.disjoint_left.mp (routes_disjoint span height tail hs hh r s hrs) he hf)
    | inr f => exact mandatory_side_intersection span height tail hs r f q he hf
  | inr e =>
    cases f with
    | inl r =>
      obtain ⟨v,hv,hr,he'⟩ := mandatory_side_intersection span height tail hs r e q hf he
      exact ⟨v,hv,he',hr⟩
    | inr f => exact side_intersection span height tail e f (fun h => hef (congrArg Sum.inr h)) q he hf

namespace Placement
open PermutationWireLayout SatCrossingLattice SignedTentacle
variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- Last actual horizontal crossing, or the clause boundary for a wire with
no horizontal crossings. The false XOR column remains at this coordinate. -/
def left (last : Option (Fin n)) : Int :=
  match last with
  | none => 0
  | some i => 512*low i+55

def LastBefore (last : Option (Fin n)) (j : Fin n) : Prop :=
  ∀ i, last=some i → i<j

def span (last : Option (Fin n)) (j : Fin n) : Nat := (512*low j-left last).toNat
def height (j : Fin n) : Nat := (512*(high p j-low j)).toNat
def tail (j : Fin n) : Nat := (512*((n:Int)+1-low j)+19).toNat

def frame (last : Option (Fin n)) (j : Fin n) : Frame :=
  ⟨true,false,false,(left last,512*low j)⟩

theorem frame_map (last : Option (Fin n)) (j : Fin n) (q : Point) :
    (frame last j).map q=(left last+q.1,512*low j+q.2) := by
  simp [frame,Frame.map,OrthogonalTentacle.place,sign]

theorem parameters (last : Option (Fin n)) (j : Fin n) (hl : LastBefore last j) :
    0≤left last ∧ 46≤span last j ∧ 9≤height p j ∧
    (span last j:Int)=512*low j-left last ∧
    (height p j:Int)=512*(high p j-low j) ∧
    (tail j:Int)=512*((n:Int)+1-low j)+19 := by
  have hj := low_bounds j
  have hh := high_bounds p j
  have hleft : 0≤left last ∧ left last+46≤512*low j := by
    cases last with
    | none => dsimp [left]; omega
    | some i =>
      have hi := low_bounds i
      have hij := low_lt_low (hl i rfl)
      dsimp [left]
      omega
  dsimp [span,height,tail]
  omega

def point (last : Option (Fin n)) (j : Fin n) (v : Fin 8) : Point :=
  (frame last j).map (vertexPoint (span last j) (height p j) (tail j) v)

def route (last : Option (Fin n)) (j : Fin n) (r : Fin 4) : List Point :=
  (SatCrossingRetirement.route (span last j) (height p j) (tail j) r).map (frame last j).map

theorem false_coordinates (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r : Fin 4) :
    point p last j (falseVertex r)=(left last,512*high p j+offset r) := by
  have hp := parameters p last j hl
  rw [point,falseVertex_coordinates,frame_map]
  apply Prod.ext
  · simp
  · dsimp
    omega

theorem true_coordinates (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r : Fin 4) :
    point p last j (trueVertex r)=(512*((n:Int)+1)+65,512*low j+offset r) := by
  have hp := parameters p last j hl
  rw [point,trueVertex_coordinates,frame_map]
  dsimp [finish]
  apply Prod.ext
  · dsimp
    omega
  · rfl

private theorem local_false_coordinates : ∀ r : Fin 4,
    XorLine.Lattice.point (x (0 : Fin 5) (falseVertex r))=(offset r+10,10) := by decide

/-- The false-side vertices of the last active section are not relocated. -/
theorem latest_false_unchanged (i j : Fin n) (hij : i <j) (r : Fin 4) :
    point p (some i) j (falseVertex r)=
      SatCrossingLattice.point p (i,j) (x 0 (falseVertex r)) := by
  rw [false_coordinates p (some i) j (by intro k hk; cases hk; exact hij),
    SatCrossingLattice.point,local_false_coordinates,SatCrossingLattice.frame_map]
  dsimp [left]
  apply Prod.ext <;> dsimp <;> omega

/-- Every point of the relevant vertical lane between its two bends belongs
to the retired mandatory arc. This will be cut at later crossing cells. -/
theorem vertical_mem (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r : Fin 4) (q : Point)
    (hx : q.1 =SatCrossingRouting.lane j r)
    (hy : 512 *low j +offset r ≤q.2 ∧ q.2 ≤512 *high p j +offset r) :
    q ∈ route p last j r := by
  have hp := parameters p last j hl
  have ht := turn_cast (span last j) hp.2.1 r
  apply List.mem_map.mpr
  refine ⟨(q.1-left last,q.2-512*low j),?_,?_⟩
  · rw [SatCrossingRetirement.route_mem,path_mem _ _ _ hp.2.1]
    apply Or.inr
    apply Or.inl
    dsimp [SatCrossingRouting.lane] at hx
    exact ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega⟩
  · rw [frame_map]
    apply Prod.ext <;> dsimp <;> omega

/-- Every future crossing row's two actual boundary ports lie on the
corresponding retired lane. No permutation of row labels is needed. -/
theorem future_row_ports (last : Option (Fin n)) (j k : Fin n)
    (hl : LastBefore last j) (hjk : SatCrossingRouting.Active p j k) (r : Fin 4) :
    SatCrossingLattice.point p (j,k) (XorLine.inputPort 4 (.inr r)) ∈ route p last j r ∧
    SatCrossingLattice.point p (j,k) (XorLine.outputPort 4 (.inr r)) ∈ route p last j r := by
  have hc := SatCrossingRouting.row_port_coordinates p (j,k) r
  have hj := low_bounds j
  have hk := high_bounds p k
  have hh := (high_lt_high p).mpr hjk.2
  have ho := offset_bounds r
  constructor
  · apply vertical_mem p last j hl r
    · rw [hc.1]
    · rw [hc.1]
      split_ifs <;> dsimp <;> omega
  · apply vertical_mem p last j hl r
    · rw [hc.2]
    · rw [hc.2]
      split_ifs <;> dsimp <;> omega

theorem route_simple (last : Option (Fin n)) (j : Fin n) (r : Fin 4) :
    (route p last j r).Nodup ∧ (route p last j r).IsChain UnitStep := by
  have hh := SatCrossingRetirement.route_simple (span last j) (height p j) (tail j) r
  constructor
  · exact hh.1.map (frame last j).injective
  · apply List.isChain_map_of_isChain (frame last j).map _ hh.2
    intro q t h
    change IntegerGrid.manhattan _ _=1
    rw [(frame last j).distance]
    exact h

theorem routes_disjoint (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r s : Fin 4) (hrs : r ≠s) :
    (route p last j r).Disjoint (route p last j s) := by
  have hp := parameters p last j hl
  have hd := SatCrossingRetirement.routes_disjoint (span last j) (height p j) (tail j)
    hp.2.1 hp.2.2.1 r s hrs
  apply List.disjoint_left.mpr
  intro q hqr hqs
  obtain ⟨u,hu,he⟩ := List.mem_map.mp hqr
  obtain ⟨v,hv,hv'⟩ := List.mem_map.mp hqs
  have huv := (frame last j).injective (he.trans hv'.symm)
  subst v
  exact List.disjoint_left.mp hd hu hv

theorem route_length_bound (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r : Fin 4) :
    (route p last j r).length≤2048*(n+1) := by
  have hp := parameters p last j hl
  have hj := low_bounds j
  have hh := high_bounds p j
  simp only [route,List.length_map,SatCrossingRetirement.route_length]
  omega

theorem coordinates_bounded (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (r : Fin 4) (q : Point) (hq : q ∈ route p last j r) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 := by
  have hp := parameters p last j hl
  have hj := low_bounds j
  have hh := high_bounds p j
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
  have hu' := SatCrossingRetirement.route_bounds _ _ _ hp.2.1 r u hu
  rw [frame_map]
  dsimp [finish] at hu'
  dsimp
  omega

/-- The full ten-edge drawing in the global permutation coordinates. -/
def edgeRoute (last : Option (Fin n)) (j : Fin n) (e : Edge) : List Point :=
  (SatCrossingRetirement.edgeRoute (span last j) (height p j) (tail j) e).map (frame last j).map

theorem point_injective (last : Option (Fin n)) (j : Fin n) :
    Function.Injective (point p last j) :=
  (frame last j).injective.comp (vertexPoint_injective _ _ _)

theorem edgeRoute_endpoints (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (e : Edge) :
    (edgeRoute p last j e).head?=some (point p last j (XorGadget.arc (edgeArc e)).1) ∧
    (edgeRoute p last j e).getLast?=some (point p last j (XorGadget.arc (edgeArc e)).2) := by
  have hp := parameters p last j hl
  have he := SatCrossingRetirement.edgeRoute_endpoints (span last j) (height p j) (tail j) hp.2.1 e
  simp only [edgeRoute,List.head?_map,List.getLast?_map,he.1,he.2,Option.map_some,point]
  exact ⟨trivial,trivial⟩

theorem edgeRoute_simple (last : Option (Fin n)) (j : Fin n) (e : Edge) :
    (edgeRoute p last j e).Nodup ∧ (edgeRoute p last j e).IsChain UnitStep := by
  have he := SatCrossingRetirement.edgeRoute_simple (span last j) (height p j) (tail j) e
  constructor
  · exact he.1.map (frame last j).injective
  · apply List.isChain_map_of_isChain (frame last j).map _ he.2
    intro q t h
    change IntegerGrid.manhattan _ _=1
    rw [(frame last j).distance]
    exact h

theorem edgeRoute_vertex_clear (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (e : Edge) (v : Fin 8) :
    point p last j v∈edgeRoute p last j e ↔
      v=(XorGadget.arc (edgeArc e)).1 ∨ v=(XorGadget.arc (edgeArc e)).2 := by
  have hp := parameters p last j hl
  rw [point,edgeRoute,List.mem_map_of_injective (frame last j).injective]
  exact SatCrossingRetirement.edgeRoute_vertex_clear _ _ _ hp.2.1 e v

theorem edgeRoute_intersection (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (e f : Edge) (hef : e ≠f) (q : Point)
    (he : q ∈edgeRoute p last j e) (hf : q ∈edgeRoute p last j f) :
    ∃ v : Fin 8, q=point p last j v ∧
      (v=(XorGadget.arc (edgeArc e)).1 ∨ v=(XorGadget.arc (edgeArc e)).2) ∧
      (v=(XorGadget.arc (edgeArc f)).1 ∨ v=(XorGadget.arc (edgeArc f)).2) := by
  have hp := parameters p last j hl
  obtain ⟨u,hu,huq⟩ := List.mem_map.mp he
  obtain ⟨w,hw,hwq⟩ := List.mem_map.mp hf
  have huw := (frame last j).injective (huq.trans hwq.symm)
  subst w
  obtain ⟨v,hv,hve,hvf⟩ := SatCrossingRetirement.edgeRoute_intersection _ _ _ hp.2.1 hp.2.2.1
    e f hef u hu hw
  refine ⟨v,?_,hve,hvf⟩
  rw [← huq,hv]
  rfl

theorem edgeRoute_length_bound (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (e : Edge) : (edgeRoute p last j e).length≤2048*(n+1) := by
  cases e with
  | inl r => exact route_length_bound p last j hl r
  | inr e =>
    have he := (sideRoute_simple (span last j) (height p j) (tail j) e).2.2.2
    simp only [edgeRoute,List.length_map,SatCrossingRetirement.edgeRoute]
    omega

theorem edgeRoute_coordinates_bounded (last : Option (Fin n)) (j : Fin n)
    (hl : LastBefore last j) (e : Edge) (q : Point) (hq : q ∈edgeRoute p last j e) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 := by
  cases e with
  | inl r => exact coordinates_bounded p last j hl r q hq
  | inr e =>
    have hp := parameters p last j hl
    have hj := low_bounds j
    have hh := high_bounds p j
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
    have hu' := sideRoute_bounds (span last j) (height p j) (tail j) e u hu
    rw [frame_map]
    dsimp [finish] at hu'
    dsimp
    omega

end Placement
end GridHardness.SatCrossingRetirement
