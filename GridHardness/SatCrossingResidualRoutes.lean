/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementHorizontal
public import GridHardness.SatCrossingRetirementCatalogue

/-!
# SAT Crossing Residual Routes

A single family of the final residual routes. The constructors contain
only extrema/emptiness facts about the actual permutation; none assumes a
geometric separation property. Distinct members have disjoint point lists.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Residual
open CliffordSynthesis PermutationWireLayout SatCrossingLattice Segments
set_option autoImplicit false
variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- The pieces of a retired lane that remain outside crossing cells and
intercell connectors after all crossings have been inserted. -/
inductive Portion (i : Fin n) where
  | unsplit (empty : EmptyColumn p i)
  | above (j : Fin n) (last : LastInColumn p i j)
  | below (j : Fin n) (first : FirstInColumn p i j)

def path (last : Option (Fin n)) (i : Fin n) (r : Fin 4) : Portion p i → List Point
  | .unsplit _ => Placement.route p last i r
  | .above j _ => upper p last i j r
  | .below j _ => lower p last i j r

theorem path_subset (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r : Fin 4) (a : Portion p i) :
    path p last i r a ⊆ Placement.route p last i r := by
  cases a with
  | unsplit he => exact fun _ h => h
  | above j hj => exact upper_subset p last i j hl hj.1 r
  | below j hj => exact lower_subset p last i j hl hj.1 r

theorem path_simple (last : Option (Fin n)) (i : Fin n) (r : Fin 4) (a : Portion p i) :
    (path p last i r a).Nodup ∧ (path p last i r a).IsChain UnitStep := by
  cases a with
  | unsplit he => exact Placement.route_simple p last i r
  | above j hj => exact upper_simple p last i j r
  | below j hj => exact lower_simple p last i j r

theorem path_length_bound (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r : Fin 4) (a : Portion p i) :
    (path p last i r a).length≤2048*(n+1) :=
  le_trans ((path_simple p last i r a).1.length_le_of_subset (path_subset p last i hl r a))
    (Placement.route_length_bound p last i hl r)

theorem path_bounds (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r : Fin 4) (a : Portion p i)
    (q : Point) (hq : q ∈path p last i r a) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 :=
  Placement.coordinates_bounded p last i hl r q (path_subset p last i hl r a hq)

theorem different_lanes (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r s : Fin 4) (hrs : r ≠s)
    (a b : Portion p i) : (path p last i r a).Disjoint (path p last i s b) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  exact List.disjoint_left.mp (Placement.routes_disjoint p last i hl r s hrs)
    (path_subset p last i hl r a hq) (path_subset p last i hl s b ht)

theorem different_wires (li lj : Option (Fin n)) (i j : Fin n)
    (hi : LastInRow p li i) (hj : LastInRow p lj j) (hij : i ≠j)
    (r s : Fin 4) (a : Portion p i) (b : Portion p j) :
    (path p li i r a).Disjoint (path p lj j s b) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  exact List.disjoint_left.mp (Separation.whole_different_wires p li lj i j hi hj hij r s)
    (path_subset p li i (lastInRow_before p li i hi) r a hq)
    (path_subset p lj j (lastInRow_before p lj j hj) s b ht)

theorem different_portions (last : Option (Fin n)) (i : Fin n)
    (hl : Placement.LastBefore last i) (r s : Fin 4)
    (a b : Portion p i) (hab : a ≠b) : (path p last i r a).Disjoint (path p last i s b) := by
  cases a with
  | unsplit he =>
    cases b with
    | unsplit hf => exact False.elim (hab rfl)
    | above j hj => exact False.elim (he j hj.1)
    | below j hj => exact False.elim (he j hj.1)
  | above j hj =>
    cases b with
    | unsplit he => exact False.elim (he j hj.1)
    | above k hk =>
      have hjk : j=k := p.injective (le_antisymm (hk.2 j hj.1) (hj.2 k hk.1))
      subst k
      exact False.elim (hab rfl)
    | below k hk => exact Segments.upper_lower_disjoint p last i k j hl hk hj r s
  | below j hj =>
    cases b with
    | unsplit he => exact False.elim (he j hj.1)
    | above k hk => exact (Segments.upper_lower_disjoint p last i j k hl hj hk s r).symm
    | below k hk =>
      have hjk : j=k := p.injective (le_antisymm (hj.2 k hk.1) (hk.2 j hj.1))
      subst k
      exact False.elim (hab rfl)

theorem path_vertical_disjoint (last : Option (Fin n)) (i a b c : Fin n)
    (hi : LastInRow p last i) (hv : SatCrossingRouting.Consecutive p a b c)
    (r s : Fin 4) (part : Portion p i) :
    (path p last i r part).Disjoint (SatCrossingRouting.route p a b c s) := by
  cases part with
  | unsplit he => exact Separation.empty_vertical_disjoint p last i a b c hi he hv r s
  | above j hj => exact Separation.upper_vertical_disjoint p last i j a b c hi hj hv r s
  | below j hj => exact Separation.lower_vertical_disjoint p last i j a b c hi hj hv r s

/-- Actual finite row-end selection supplies the placement parameter. -/
def rowEnd (i : Fin n) : Option (Fin n) := Catalogue.lastRequest? p i

theorem rowEnd_valid (i : Fin n) : LastInRow p (rowEnd p i) i := by
  cases he : Catalogue.lastRequest? p i with
  | none => simpa [rowEnd,he,LastInRow] using (Catalogue.lastRequest_none p i).mp he
  | some j => simpa [rowEnd,he,LastInRow] using Catalogue.lastRequest_sound p j i he

abbrev Index := (i : Fin n) × (Fin 4 × Portion p i)

def route (v : Index p) : List Point := path p (rowEnd p v.1) v.1 v.2.1 v.2.2

/-- Pairwise disjointness of the entire final residual family, covering all
wires, all four lanes, and all upper/lower/empty cases simultaneously. -/
theorem route_disjoint (v w : Index p) (hvw : v ≠w) : (route p v).Disjoint (route p w) := by
  rcases v with ⟨i,r,a⟩
  rcases w with ⟨j,s,b⟩
  by_cases hij : i=j
  · subst j
    by_cases hrs : r=s
    · subst s
      have hab : a≠b := fun h => hvw (by cases h; rfl)
      exact different_portions p (rowEnd p i) i
        (lastInRow_before p _ i (rowEnd_valid p i)) r r a b hab
    · exact different_lanes p (rowEnd p i) i
        (lastInRow_before p _ i (rowEnd_valid p i)) r s hrs a b
  · exact different_wires p (rowEnd p i) (rowEnd p j) i j
      (rowEnd_valid p i) (rowEnd_valid p j) hij r s a b

theorem route_vertical_disjoint (v : Index p) (a b c : Fin n)
    (hv : SatCrossingRouting.Consecutive p a b c) (s : Fin 4) :
    (route p v).Disjoint (SatCrossingRouting.route p a b c s) :=
  path_vertical_disjoint p (rowEnd p v.1) v.1 a b c (rowEnd_valid p v.1) hv v.2.1 s v.2.2

theorem route_simple (v : Index p) :
    (route p v).Nodup ∧ (route p v).IsChain UnitStep :=
  path_simple p (rowEnd p v.1) v.1 v.2.1 v.2.2

theorem route_length_bound (v : Index p) : (route p v).length≤2048*(n+1) :=
  path_length_bound p (rowEnd p v.1) v.1
    (lastInRow_before p _ v.1 (rowEnd_valid p v.1)) v.2.1 v.2.2

theorem route_bounds (v : Index p) (q : Point) (hq : q ∈route p v) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+516 :=
  path_bounds p (rowEnd p v.1) v.1
    (lastInRow_before p _ v.1 (rowEnd_valid p v.1)) v.2.1 v.2.2 q hq

def upperAt (i : Fin n) (part : Portion p i) (j : Fin n) : Prop :=
  match part with
  | .above b _ => b=j
  | _ => False

def lowerAt (i : Fin n) (part : Portion p i) (j : Fin n) : Prop :=
  match part with
  | .below b _ => b=j
  | _ => False

/-- Exact intersections of the entire residual family with an upper
horizontal connector. The common point is an endpoint of both routes. -/
theorem route_upper_intersection_iff (v : Index p) (i k j : Fin n)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (q : Point) :
    (q∈route p v ∧ q∈SatCrossingHorizontal.upperRoute p i k j) ↔
      v.1=i ∧ v.2.1=0 ∧ upperAt p v.1 v.2.2 j ∧
        q=point p (i,j) (XorLine.row 0 false) := by
  rcases v with ⟨a,r,part⟩
  have ha := rowEnd_valid p a
  cases part with
  | unsplit he =>
    constructor
    · rintro ⟨hq,ht⟩
      exact False.elim (List.disjoint_left.mp
        (Connections.empty_horizontal_disjoint p (rowEnd p a) a i k j ha he hh r).1 hq ht)
    · rintro ⟨_,_,h,_⟩
      exact False.elim h
  | above b hb =>
    have he := Connections.upper_upper_intersection_iff p (rowEnd p a) a b i k j ha hb hh r q
    constructor
    · intro h
      have ht := he.mp h
      exact ⟨ht.1,ht.2.2.1,ht.2.1,ht.2.2.2⟩
    · rintro ⟨hai,hr,hb,hq⟩
      exact he.mpr ⟨hai,hb,hr,hq⟩
  | below b hb =>
    constructor
    · rintro ⟨hq,ht⟩
      exact False.elim (List.disjoint_left.mp
        (Connections.lower_upper_disjoint p (rowEnd p a) a b i k j ha hb hh r) hq ht)
    · rintro ⟨_,_,h,_⟩
      exact False.elim h

theorem route_lower_intersection_iff (v : Index p) (i k j : Fin n)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (q : Point) :
    (q∈route p v ∧ q∈SatCrossingHorizontal.lowerRoute p i k j) ↔
      v.1=i ∧ v.2.1=0 ∧ lowerAt p v.1 v.2.2 j ∧
        q=point p (i,j) (XorLine.row 0 true) := by
  rcases v with ⟨a,r,part⟩
  have ha := rowEnd_valid p a
  cases part with
  | unsplit he =>
    constructor
    · rintro ⟨hq,ht⟩
      exact False.elim (List.disjoint_left.mp
        (Connections.empty_horizontal_disjoint p (rowEnd p a) a i k j ha he hh r).2 hq ht)
    · rintro ⟨_,_,h,_⟩
      exact False.elim h
  | above b hb =>
    constructor
    · rintro ⟨hq,ht⟩
      exact False.elim (List.disjoint_left.mp
        (Connections.upper_lower_disjoint p (rowEnd p a) a b i k j ha hb hh r) hq ht)
    · rintro ⟨_,_,h,_⟩
      exact False.elim h
  | below b hb =>
    have he := Connections.lower_lower_intersection_iff p (rowEnd p a) a b i k j ha hb hh r q
    constructor
    · intro h
      have ht := he.mp h
      exact ⟨ht.1,ht.2.2.1,ht.2.1,ht.2.2.2⟩
    · rintro ⟨hai,hr,hb,hq⟩
      exact he.mpr ⟨hai,hb,hr,hq⟩

end GridHardness.SatCrossingRetirement.Residual
