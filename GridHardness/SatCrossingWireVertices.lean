/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementCatalogue

/-!
# SAT Crossing Wire Vertices

Simultaneous placement of all retired XOR vertices and forty-vertex
crossing remnants. This is the wire-vertex placement; routes and the variable,
clause and sentinel bodies are supplied by their respective drawing modules.
-/

@[expose] public section

namespace GridHardness.SatCrossingWireVertices
open PermutationWireLayout SatCrossingRetirement
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))

def retired (j : Fin n) (v : Fin 8) : Int × Int :=
  Placement.point p (Catalogue.lastRequest? p j) j v

private theorem left_bound (last : Option (Fin n)) : Placement.left last≤512*n+55 := by
  cases last with
  | none => dsimp [Placement.left]; omega
  | some i =>
    have hi := low_bounds i
    dsimp [Placement.left]
    omega

theorem retired_injective : Function.Injective (fun jv : Fin n × Fin 8 => retired p jv.1 jv.2) := by
  rintro ⟨j,v⟩ ⟨k,w⟩ he
  have hv := Catalogue.last_before p j
  have hw := Catalogue.last_before p k
  have hjk : j=k := by
    obtain ⟨r,hr⟩ := vertex_split v
    obtain ⟨s,hs⟩ := vertex_split w
    have hor := offset_bounds r
    have hos := offset_bounds s
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · simp only [retired,Placement.true_coordinates p _ j hv,
        Placement.true_coordinates p _ k hw] at hx hy
      apply low_injective
      omega
    · simp only [retired,Placement.true_coordinates p _ j hv,
        Placement.false_coordinates p _ k hw] at hx
      have hb := left_bound (Catalogue.lastRequest? p k)
      omega
    · simp only [retired,Placement.false_coordinates p _ j hv,
        Placement.true_coordinates p _ k hw] at hx
      have hb := left_bound (Catalogue.lastRequest? p j)
      omega
    · simp only [retired,Placement.false_coordinates p _ j hv,
        Placement.false_coordinates p _ k hw] at hy
      apply high_injective p
      omega
  subst k
  exact Prod.ext rfl (Placement.point_injective p _ j he)

theorem retired_ne_retained (j : Fin n) (v : Fin 8) (c : SatCrossingLattice.Cell n)
    (w : SatCrossingHorizontal.RetainedVertex) :
    retired p j v ≠ SatCrossingLattice.point p c w.val := by
  intro he
  have hl := Catalogue.last_before p j
  obtain ⟨r,hr⟩ := vertex_split v
  rcases hr with rfl | rfl
  · have hb := SatCrossingLattice.coordinates_bounded p c _
      (SatCrossingLattice.point_in_box p c w.val)
    have hx := congrArg Prod.fst he
    simp only [retired,Placement.true_coordinates p _ j hl] at hx
    omega
  · cases hc : Catalogue.lastRequest? p j with
    | none =>
      have hb := SatCrossingLattice.point_in_box p c w.val
      have hlow := low_bounds c.1
      have hx := congrArg Prod.fst he
      simp only [retired,hc] at hx
      rw [Placement.false_coordinates p none j (by intro k hk; cases hk) r] at hx
      change (0 : Int)=(SatCrossingLattice.point p c w.val).1 at hx
      dsimp [SatCrossingLattice.InBox] at hb
      omega
    | some i =>
      have hij := (Catalogue.lastRequest_sound p i j hc).1.1
      change Placement.point p (Catalogue.lastRequest? p j) j (falseVertex r) = _ at he
      rw [hc,Placement.latest_false_unchanged p i j hij r] at he
      have he' := @SatCrossingLattice.point_injective n p
        ((i,j),XorLine.x 0 (falseVertex r)) (c,w.val) he
      exact SatCrossingHorizontal.retained_ne_zero w (falseVertex r) (congrArg Prod.snd he')

abbrev Vertex := (Fin n × Fin 8) ⊕
  (WireCrossingSchedule.Cell p × SatCrossingHorizontal.RetainedVertex)

def point : Vertex p → Int × Int
  | .inl (j,v) => retired p j v
  | .inr (c,v) => SatCrossingLattice.point p c.val v.val

theorem point_injective : Function.Injective (point p) := by
  intro u v he
  cases u with
  | inl jv =>
    cases v with
    | inl kw => exact congrArg Sum.inl (retired_injective p he)
    | inr cv => exact False.elim (retired_ne_retained p jv.1 jv.2 cv.1.val cv.2 he)
  | inr cv =>
    cases v with
    | inl jv => exact False.elim (retired_ne_retained p jv.1 jv.2 cv.1.val cv.2 he.symm)
    | inr dw =>
      have h := @SatCrossingLattice.point_injective n p (cv.1.val,cv.2.val)
        (dw.1.val,dw.2.val) he
      exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h)))

theorem retired_bounds (j : Fin n) (v : Fin 8) :
    0≤(retired p j v).1 ∧ (retired p j v).1≤512*(n+1)+65 ∧
      0≤(retired p j v).2 ∧ (retired p j v).2≤1024*n+522 := by
  have hl := Catalogue.last_before p j
  have hp := Placement.parameters p (Catalogue.lastRequest? p j) j hl
  have hj := low_bounds j
  have hh := high_bounds p j
  have hleft := left_bound (Catalogue.lastRequest? p j)
  obtain ⟨r,hr⟩ := vertex_split v
  have ho := offset_bounds r
  rcases hr with rfl | rfl
  · simp only [retired,Placement.true_coordinates p _ j hl]
    omega
  · simp only [retired,Placement.false_coordinates p _ j hl]
    omega

theorem point_bounds (v : Vertex p) :
    0≤(point p v).1 ∧ (point p v).1≤512*(n+1)+65 ∧
      0≤(point p v).2 ∧ (point p v).2≤1024*n+522 := by
  cases v with
  | inl jv => exact retired_bounds p jv.1 jv.2
  | inr cv =>
    have h := SatCrossingLattice.coordinates_bounded p cv.1.val _
      (SatCrossingLattice.point_in_box p cv.1.val cv.2.val)
    change 0≤_ ∧ _≤_ ∧ 0≤_ ∧ _≤_
    dsimp [point]
    omega

end GridHardness.SatCrossingWireVertices
