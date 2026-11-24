/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCoreSeparation

/-!
# Lattice Route Indexed Separation

Quantitative separation by route indices. On a simple dilated lattice
route, points that are far apart in traversal order remain separated until
the full dilation margin is reached.
-/

@[expose] public section

namespace GridHardness.LatticeSubdivision
open CliffordSynthesis
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Any indexed point lies on an indexed original edge, including the
final point by allowing the last edge's closed terminal parameter. -/
theorem subdivide_getElem_edge (s : Nat) (_hs : 0 <s) (l : List Point)
    (hl : 2 ≤l.length) (i : Nat) (hi : i <(subdivide s l).length) :
    ∃ k t : Nat, ∃ hk : k+1<l.length, t≤s ∧ i=s*k+t ∧
      (subdivide s l)[i]=interpolate s (l[k]'(by omega)) (l[k+1]'hk) t := by
  induction l generalizing i with
  | nil => simp at hl
  | cons p l ih =>
    cases l with
    | nil => simp at hl
    | cons q l =>
      by_cases his : i<s
      · refine ⟨0,i,by simp,by omega,by omega,?_⟩
        exact subdivide_getElem_initial s (p::q::l) (by simp) i his
      · cases l with
        | nil =>
          have hlen := subdivide_length s [p,q] (by simp)
          have hei : i=s := by simpa using (by simp at hlen; omega : i=s)
          subst i
          refine ⟨0,s,by simp,by omega,by omega,?_⟩
          rw [interpolate_scale]
          change (segmentInit s p q++[scale s q])[s]=scale s q
          rw [List.getElem_append_right (by rw [segmentInit_length])]
          simp [segmentInit_length]
        | cons r l =>
          have hilen : i-s<(subdivide s (q::r::l)).length := by
            rw [subdivide,List.length_append,segmentInit_length] at hi
            omega
          obtain ⟨k,t,hk,ht,he,hpoint⟩ := ih (by simp) (i-s) hilen
          refine ⟨k+1,t,by simp at hk ⊢; omega,ht,by simp only [Nat.mul_add,Nat.mul_one]; omega,?_⟩
          change (segmentInit s p q++subdivide s (q::r::l))[i]=
            interpolate s ((q::r::l)[k]) ((q::r::l)[k+1]) t
          rw [List.getElem_append_right (by rw [segmentInit_length]; omega)]
          simpa only [segmentInit_length] using hpoint

/-- The distance along one original edge equals its parameter difference. -/
theorem interpolate_same_edge_distance (s : Nat) {p q : Point} (h : UnitStep p q)
    (t r : Nat) :
    IntegerGrid.manhattan (interpolate s p q t) (interpolate s p q r)=
      Int.natAbs ((t : Int)-r) := by
  rcases (manhattan_one_iff p q).mp h with rfl | rfl | rfl | rfl <;>
    simp [interpolate,IntegerGrid.manhattan] <;> omega

/-- Pointwise clearance controlled by the smaller of the dilation factor
and the distance between the two traversal indices. -/
theorem subdivide_index_distance (s : Nat) (hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (i j : Nat) (hi : i <(subdivide s l).length) (hj : j <(subdivide s l).length)
    (hij : i ≤j) :
    min s (j-i)≤IntegerGrid.manhattan ((subdivide s l)[i]) ((subdivide s l)[j]) := by
  obtain ⟨a,t,ha,ht,hi',hpi⟩ := subdivide_getElem_edge s hs l hl i hi
  obtain ⟨b,r,hb,hr,hj',hpj⟩ := subdivide_getElem_edge s hs l hl j hj
  rw [hpi,hpj]
  have hua : UnitStep (l[a]'(by omega)) (l[a+1]'ha) :=
    List.isChain_iff_getElem.mp hc a ha
  have hub : UnitStep (l[b]'(by omega)) (l[b+1]'hb) :=
    List.isChain_iff_getElem.mp hc b hb
  have hneq : ∀ (u v : Nat) (hu : u<l.length) (hv : v<l.length),
      u≠v → (l[u]'hu)≠(l[v]'hv) := by
    intro u v hu hv huv he
    exact huv (hn.getElem_inj_iff.mp he)
  by_cases hab : a=b
  · subst b
    rw [interpolate_same_edge_distance s hua]
    have htr : t≤r := by omega
    have hd : Int.natAbs ((t : Int)-r)=r-t := by omega
    rw [hd]
    omega
  by_cases hab1 : a+1=b
  · subst b
    have hneq' := hneq a (a+1+1) (by omega) hb (by omega)
    have hua' : UnitStep (l[a+1]'ha) (l[a]'(by omega)) := by
      simpa only [UnitStep,IntegerGrid.manhattan_comm] using hua
    have he := LatticeRouteCore.common_source_distance s hua' hub hneq' (s-t) r
    rw [← interpolate_reverse s (l[a]'(by omega)) (l[a+1]'ha) ht] at he
    rw [he]
    simp only [Nat.mul_add,Nat.mul_one] at hi' hj'
    omega
  by_cases hba1 : b+1=a
  · subst a
    have hneq' := hneq (b+1+1) b ha (by omega) (by omega)
    have hub' : UnitStep (l[b+1]'hb) (l[b]'(by omega)) := by
      simpa only [UnitStep,IntegerGrid.manhattan_comm] using hub
    have he := LatticeRouteCore.common_source_distance s hua hub' hneq' t (s-r)
    rw [← interpolate_reverse s (l[b]'(by omega)) (l[b+1]'hb) hr] at he
    rw [he]
    simp only [Nat.mul_add,Nat.mul_one] at hi' hj'
    omega
  · exact (Nat.min_le_left s (j-i)).trans (interpolate_separation s hua hub
      (hneq a b (by omega) (by omega) hab)
      (hneq a (b+1) (by omega) hb (by omega))
      (hneq (a+1) b ha (by omega) hab1)
      (hneq (a+1) (b+1) ha hb (by omega)) ht hr)

end GridHardness.LatticeSubdivision

namespace GridHardness.LatticeRouteCore
open CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Traversal-index separation up to a fixed geometric margin. -/
def IndexSeparated (s : Nat) (l : List Point) : Prop :=
  ∀ i j (hi : i<l.length) (hj : j<l.length), i≤j →
    min s (j-i)≤IntegerGrid.manhattan (l[i]'hi) (l[j]'hj)

theorem indexSeparated_trim (s a b : Nat) (l : List Point) (h : IndexSeparated s l) :
    IndexSeparated s (LatticeRouteTrim.trim a b l) := by
  intro i j hi hj hij
  rw [LatticeRouteTrim.getElem,LatticeRouteTrim.getElem]
  have hh := h (a+i) (a+j) (by rw [LatticeRouteTrim.length] at hi; omega)
    (by rw [LatticeRouteTrim.length] at hj; omega) (by omega)
  simpa only [Nat.add_sub_add_left] using hh

theorem indexSeparated_reverse (s : Nat) (l : List Point) (h : IndexSeparated s l) :
    IndexSeparated s l.reverse := by
  intro i j hi hj hij
  simp only [List.length_reverse] at hi hj
  rw [List.getElem_reverse,List.getElem_reverse,IntegerGrid.manhattan_comm]
  have hh := h (l.length-1-j) (l.length-1-i) (by omega) (by omega) (by omega)
  have he : (l.length-1-i)-(l.length-1-j)=j-i := by omega
  simpa only [he] using hh

theorem indexSeparated_orient (s : Nat) (l : List Point) (h : IndexSeparated s l) (b : Bool) :
    IndexSeparated s (LatticeRouteDirections.orient l b) := by
  cases b
  · exact h
  · exact indexSeparated_reverse s l h

/-- The central route inherits index separation independently of its
endpoint cuts, even when a cut removes more than one whole run. -/
theorem core_indexSeparated (s a b : Nat) (hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length) :
    IndexSeparated s (core s a b l) :=
  indexSeparated_trim s a b (subdivide s l)
    (subdivide_index_distance s hs l hn hc hl)

end GridHardness.LatticeRouteCore
