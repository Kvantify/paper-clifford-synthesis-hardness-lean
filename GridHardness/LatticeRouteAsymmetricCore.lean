/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCore
public import GridHardness.LatticeRouteIndexedSeparation

/-!
# Lattice Route Asymmetric Core

Exact endpoints and port directions after unequal endpoint cuts of a
scaled simple route. This includes the short owner cut and the side-dependent
recipient cut used to join the actual cluster docks.
-/

public section

namespace GridHardness.LatticeRouteCore
open CliffordSynthesis LatticeSubdivision LatticeRouteDirections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev UnitStep := LatticeRouteDirections.UnitStep

private theorem subdivide_minLength (s : Nat) (l : List Point) (hl : 2 ≤l.length) :
    s+1≤(subdivide s l).length := by
  have hn : l≠[] := by intro he; simp [he] at hl
  rw [subdivide_length s l hn]
  have h := Nat.mul_le_mul_left s (show 1≤l.length-1 by omega)
  simpa using Nat.add_le_add_right h 1

theorem certificate (s a b : Nat) (hs : 0 <s) (hab : a +b<s)
    (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length) :
    (core s a b l).head?=some (interpolate s (endpointPoint l false hl)
      (neighborPoint l false hl) a) ∧
    (core s a b l).getLast?=some (interpolate s (endpointPoint l true hl)
      (neighborPoint l true hl) b) ∧
    (core s a b l).Nodup ∧ (core s a b l).IsChain UnitStep ∧
    s+1-a-b≤(core s a b l).length ∧ (core s a b l).length≤s*l.length := by
  have hne : l≠[] := by intro he; simp [he] at hl
  have hlen := subdivide_length s l hne
  have hmin := subdivide_minLength s l hl
  have hcLen : (core s a b l).length=(subdivide s l).length-a-b := LatticeRouteTrim.length _ _ _
  refine ⟨?_,?_,LatticeRouteTrim.nodup a b _ (subdivide_nodup s l hn hc),
    LatticeRouteTrim.chain a b _ (subdivide_chain s hs l hc),by omega,?_⟩
  · rw [core,LatticeRouteTrim.head a b _ (by omega),subdivide_getElem_initial s l hl a (by omega)]
    rfl
  · rw [core,LatticeRouteTrim.getLast a b _ (by omega),
      subdivide_getElem_terminal s hs l hl b (by omega)]
    apply congrArg some
    simp [endpointPoint,neighborPoint,orient,Nat.sub_sub]
  · have hbound := subdivide_length_le s hs l
    omega

theorem interpolate_step (s : Nat) {p q : Point} (h : UnitStep p q) (k : Nat) :
    interpolate s p q (k+1)=step (interpolate s p q k) (direction p q) := by
  have he := LatticeRouteDirections.direction_spec p q h
  generalize direction p q=d at he ⊢
  rw [he]
  fin_cases d <;> simp [interpolate,scale,step,DirectedLocalLayout.ray] <;> omega

theorem initial_two (s a b : Nat) (hs : 0 <s) (hab : a +b+1<s)
    (l : List Point) (hl : 2 ≤l.length) (k : Nat) (hk : k ≤1) :
    (core s a b l)[k]'(by
      have hn : l≠[] := by intro he; simp [he] at hl
      have he := subdivide_length s l hn
      have hmin := subdivide_minLength s l hl
      rw [core,LatticeRouteTrim.length]; omega)=
      interpolate s (endpointPoint l false hl) (neighborPoint l false hl) (a+k) := by
  change (LatticeRouteTrim.trim a b (subdivide s l))[k]'_ = _
  rw [LatticeRouteTrim.getElem,subdivide_getElem_initial s l hl (a+k) (by omega)]
  rfl

theorem terminal_two (s a b : Nat) (hs : 0 <s) (hab : a +b+1<s)
    (l : List Point) (hl : 2 ≤l.length) (k : Nat) (hk : k ≤1) :
    (core s a b l)[(core s a b l).length-1-k]'(by
      have hn : l≠[] := by intro he; simp [he] at hl
      have he := subdivide_length s l hn
      have hmin := subdivide_minLength s l hl
      rw [core,LatticeRouteTrim.length]; omega)=
      interpolate s (endpointPoint l true hl) (neighborPoint l true hl) (b+k) := by
  have hn : l≠[] := by intro he; simp [he] at hl
  have he := subdivide_length s l hn
  have hmin := subdivide_minLength s l hl
  change (LatticeRouteTrim.trim a b (subdivide s l))[(core s a b l).length-1-k]'_ = _
  rw [LatticeRouteTrim.getElem]
  have hi : a+((core s a b l).length-1-k)=(subdivide s l).length-1-(b+k) := by
    rw [core,LatticeRouteTrim.length]; omega
  simp only [hi]
  rw [subdivide_getElem_terminal s hs l hl (b+k) (by omega)]
  simp [endpointPoint,neighborPoint,orient,Nat.sub_sub]

/-- Both retained endpoint directions equal the original outgoing ports. -/
theorem tangent_eq (s a b : Nat) (hs : 0 <s) (hab : a +b+1<s)
    (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (t : Bool) :
    tangent (core s a b l) t (by
      have hh := (certificate s a b hs (by omega) l hn hc hl).2.2.2.2.1; omega)=
      tangent l t hl := by
  have hcLen : 2≤(core s a b l).length := by
    have hh := (certificate s a b hs (by omega) l hn hc hl).2.2.2.2.1; omega
  cases t
  · have h0 : endpointPoint (core s a b l) false hcLen =
        interpolate s (endpointPoint l false hl) (neighborPoint l false hl) a := by
      change (core s a b l)[0]'_= _
      simpa only [Nat.add_zero] using initial_two s a b hs hab l hl 0 (by decide)
    have h1 : neighborPoint (core s a b l) false hcLen =
        interpolate s (endpointPoint l false hl) (neighborPoint l false hl) (a+1) :=
      initial_two s a b hs hab l hl 1 (by decide)
    change direction (endpointPoint (core s a b l) false hcLen)
      (neighborPoint (core s a b l) false hcLen)=_
    rw [h0,h1]
    rw [interpolate_step s (neighborPoint_step l false hl hc) a,direction_step]
    rfl
  · have h0 : endpointPoint (core s a b l) true hcLen =
        interpolate s (endpointPoint l true hl) (neighborPoint l true hl) b := by
      change (core s a b l).reverse[0]'_= _
      rw [List.getElem_reverse]
      simpa only [Nat.sub_zero,Nat.add_zero] using terminal_two s a b hs hab l hl 0 (by decide)
    have h1 : neighborPoint (core s a b l) true hcLen =
        interpolate s (endpointPoint l true hl) (neighborPoint l true hl) (b+1) := by
      change (core s a b l).reverse[1]'_= _
      rw [List.getElem_reverse]
      exact terminal_two s a b hs hab l hl 1 (by decide)
    change direction (endpointPoint (core s a b l) true hcLen)
      (neighborPoint (core s a b l) true hcLen)=_
    rw [h0,h1]
    rw [interpolate_step s (neighborPoint_step l true hl hc) b,direction_step]
    rfl

end GridHardness.LatticeRouteCore
