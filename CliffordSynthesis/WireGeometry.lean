/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.CircuitLedger
public import CliffordSynthesis.PairGeometry

/-!
# Wire Geometry

Geometry of labelled physical wires, used to maintain untouched pairs.
-/

@[expose] public section

namespace CliffordSynthesis.WireGeometry

open LinearMap (BilinForm)
open Planes (F plane)
open SymplecticCircuit (Rows IsSymplectic H S CX)
open Observation (visible)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

def wire (a : Rows n V) (i : Fin n) : Submodule F V := plane (a.x i) (a.z i)

def joint (a : Rows n V) (i j : Fin n) : Submodule F V := wire a i ⊔ wire a j

theorem wire_pair (B : BilinForm F V) (a : Rows n V) (ha : IsSymplectic B a) (i : Fin n) :
    Planes.SymplecticPair B (a.x i) (a.z i) := by
  constructor <;> simp [ha.xx, ha.xz, ha.zx, ha.zz]

theorem visible_spec (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a) (i : Fin n) (u : V) :
    visible W a i = some u ↔ u ≠ 0 ∧ u ∈ W ⊓ wire a i :=
  Observation.observe_eq_some B W hW _ _ (wire_pair B a ha i) u

theorem hidden_iff (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a) (i : Fin n) :
    visible W a i = none ↔ W ⊓ wire a i = ⊥ := by
  constructor
  · intro hi
    apply le_antisymm _ bot_le
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · have hs := (visible_spec B W hW a ha i u).mpr ⟨hu0, hu⟩
      rw [hi] at hs
      contradiction
  · intro hi
    cases hv : visible W a i with
    | none => rfl
    | some u =>
      have hu := (visible_spec B W hW a ha i u).mp hv
      have hu0 : u = 0 := by simpa [hi] using hu.2
      exact False.elim (hu.1 hu0)

theorem H_wire (a : Rows n V) (q i : Fin n) : wire (H q a) i = wire a i := by
  by_cases hi : i = q <;> simp [wire, H, hi, Planes.hadamard_plane]

theorem S_wire (a : Rows n V) (q i : Fin n) : wire (S q a) i = wire a i := by
  by_cases hi : i = q <;> simp [wire, S, hi, Planes.phase_plane]

theorem CX_wire (a : Rows n V) (c t i : Fin n) (hic : i ≠ c) (hit : i ≠ t) :
    wire (CX c t a) i = wire a i := by simp [wire, CX, hic, hit]

theorem CX_joint (a : Rows n V) (c t : Fin n) (hct : c ≠ t) :
    joint (CX c t a) c t = joint a c t := by
  simpa [joint, wire, CX, hct, Ne.symm hct, PairGeometry.joint] using
    PairGeometry.cnot_joint (a.x c) (a.z c) (a.x t) (a.z t)

theorem wire_orthogonal (B : BilinForm F V) (a : Rows n V) (ha : IsSymplectic B a)
    (i j : Fin n) (hij : i ≠ j) : wire a j ≤ B.orthogonal (wire a i) := by
  intro q hq p hp
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨z, w, rfl⟩ := Submodule.mem_span_pair.mp hq
  simp [map_add, map_smul, ha.xx, ha.xz, ha.zx, ha.zz, hij]

/-- Distinct physical wires cannot display the same nonzero vector. -/
theorem visible_distinct (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i j : Fin n) (hij : i ≠ j) (u v : V)
    (hu : visible W a i = some u) (hv : visible W a j = some v) : u ≠ v := by
  intro huv
  subst v
  have hui := (visible_spec B W hW a ha i u).mp hu
  have huj := (visible_spec B W hW a ha j u).mp hv
  have hx := wire_orthogonal B a ha i j hij huj.2.2 (a.x i)
    ((Planes.mem_plane_iff _ _ _).mpr (Or.inr (Or.inl rfl)))
  have hz := wire_orthogonal B a ha i j hij huj.2.2 (a.z i)
    ((Planes.mem_plane_iff _ _ _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  rcases (Planes.mem_plane_iff _ _ _).mp hui.2.2 with h | h | h | h
  · exact hui.1 h
  · simp [h, ha.zx] at hz
  · simp [h, ha.xz] at hx
  · simp [h, map_add, ha.xx, ha.xz] at hx

theorem outside_orthogonal (B : BilinForm F V) (a : Rows n V) (ha : IsSymplectic B a)
    (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    wire a k ≤ B.orthogonal (joint a i j) := by
  intro q hq p hp
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hp
  simp [map_add, wire_orthogonal B a ha i k hik hq u hu,
    wire_orthogonal B a ha j k hjk hq v hv]

theorem visible_pair_lagrangian (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i j : Fin n) (hij : i ≠ j) (u v : V)
    (hu : visible W a i = some u) (hv : visible W a j = some v) :
    W ⊓ joint a i j = plane u v ∧
      Splitting.LagrangianIn B (W ⊓ joint a i j) (joint a i j) := by
  have hu' := (visible_spec B W hW a ha i u).mp hu
  have hv' := (visible_spec B W hW a ha j v).mp hv
  exact PairGeometry.visible_pair_lagrangian B W hW _ _ _ _
    (SymplecticCircuit.endpoint_frame B a ha i j hij) hu'.2 hv'.2 hu'.1 hv'.1

/-- If the joint intersection is zero, a CNOT cannot create a visible endpoint. -/
theorem CX_hidden_of_joint (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (c t : Fin n) (hct : c ≠ t) (hz : W ⊓ joint a c t = ⊥) :
    visible W (CX c t a) c = none ∧ visible W (CX c t a) t = none := by
  have ha' := SymplecticCircuit.CX_symplectic B a ha c t hct
  have hj : W ⊓ joint (CX c t a) c t = ⊥ := by rw [CX_joint a c t hct, hz]
  constructor
  · apply (hidden_iff B W hW _ ha' c).mpr
    apply le_antisymm _ bot_le
    exact (inf_le_inf_left W le_sup_left).trans (le_of_eq hj)
  · apply (hidden_iff B W hW _ ha' t).mpr
    apply le_antisymm _ bot_le
    exact (inf_le_inf_left W le_sup_right).trans (le_of_eq hj)

theorem cross_joint_zero (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (hlag : Splitting.LagrangianIn B (W ⊓ joint a i j) (joint a i j))
    (hi : visible W a i = none) (hk : visible W a k = none) :
    W ⊓ joint a i k = ⊥ :=
  Splitting.no_cross_pair B W (joint a i j) (wire a i) (wire a k) hW hlag
    le_sup_left (outside_orthogonal B a ha i j k hik hjk)
    ((hidden_iff B W hW a ha i).mp hi) ((hidden_iff B W hW a ha k).mp hk)

/-- The first endpoint of an untouched pair cannot return together with a
different hidden wire. The pairing invariant is geometric, not an assumption
about the gate's event classification. -/
theorem no_cross_return (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (hlag : Splitting.LagrangianIn B (W ⊓ joint a i j) (joint a i j))
    (hi : visible W a i = none) (hk : visible W a k = none) :
    visible W (CX i k a) i = none ∧ visible W (CX i k a) k = none := by
  apply CX_hidden_of_joint B W hW a ha i k hik
  exact cross_joint_zero B W hW a ha i j k hik hjk hlag hi hk

/-- In a Lagrangian joint intersection, one visible endpoint forces the other
endpoint to be visible. This excludes a type P return on a listed pair. -/
theorem lagrangian_visible_partner (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i j : Fin n) (hij : i ≠ j)
    (hlag : Splitting.LagrangianIn B (W ⊓ joint a i j) (joint a i j))
    (hi : (visible W a i).isSome = true) : (visible W a j).isSome = true := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
  have hu' := (visible_spec B W hW a ha i u).mp hu
  cases hj : visible W a j with
  | some v => rfl
  | none =>
    have hjzero := (hidden_iff B W hW a ha j).mp hj
    have hsub : W ⊓ joint a i j ≤ wire a i := by
      intro w hw
      obtain ⟨p, hp, q, hq, heq⟩ := Submodule.mem_sup.mp hw.2
      have hup : B u p = 0 := by
        have hz := hW hw.1 u hu'.2.1
        rw [← heq, map_add, wire_orthogonal B a ha i j hij hq u hu'.2.2,
          add_zero] at hz
        exact hz
      have hpW : p ∈ W :=
        (Submodule.span_le.mpr (by simpa using hu'.2.1))
          (Planes.orthogonal_line B _ _ (wire_pair B a ha i) hu'.2.2 hp hu'.1 hup)
      have hqW : q ∈ W := by simpa [← heq] using W.sub_mem hw.1 hpW
      have hq0 : q = 0 := by
        have : q ∈ W ⊓ wire a j := ⟨hqW, hq⟩
        simpa [hjzero] using this
      simpa [← heq, hq0] using hp
    have hxj : a.x j ∈ wire a j := Submodule.subset_span (by simp)
    have hx : a.x j ∈ joint a i j ⊓ B.orthogonal (W ⊓ joint a i j) := by
      refine ⟨Submodule.mem_sup_right hxj, ?_⟩
      intro w hw
      exact wire_orthogonal B a ha i j hij hxj w (hsub hw)
    rw [hlag.2] at hx
    have hxzero : a.x j = 0 := by
      have : a.x j ∈ W ⊓ wire a j := ⟨hx.1, hxj⟩
      simpa [hjzero] using this
    have hxz := ha.xz j j
    simp [hxzero] at hxz

end CliffordSynthesis.WireGeometry
