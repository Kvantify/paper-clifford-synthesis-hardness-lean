/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.LocalChart

/-!
# Pair Geometry

The Lagrangian of a visible pair and its symplectic summand.
These are the geometric invariants that a D event stores.
-/

@[expose] public section

namespace CliffordSynthesis.PairGeometry

open LinearMap (BilinForm)
open Planes (F plane)
open LocalChart (Frame chart bit)

variable {V : Type*} [AddCommGroup V] [Module F V]

def joint (a b c d : V) : Submodule F V := plane a b ⊔ plane c d

private theorem cross (B : BilinForm F V) (a b c d : V) (h : Frame B a b c d)
    {p q : V} (hp : p ∈ plane a b) (hq : q ∈ plane c d) : B p q = 0 ∧ B q p = 0 := by
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨z, w, rfl⟩ := Submodule.mem_span_pair.mp hq
  simp [map_add, map_smul, h.ac, h.ad, h.bc, h.bd, h.ca, h.cb, h.da, h.db]

/-- Visible vectors on two orthogonal qubits span the whole local W intersection,
and form a Lagrangian in the joint four-dimensional symplectic space. -/
theorem visible_pair_lagrangian (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V) (h : Frame B a b c d)
    {u v : V} (hu : u ∈ W ⊓ plane a b) (hv : v ∈ W ⊓ plane c d)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    W ⊓ joint a b c d = Submodule.span F {u, v} ∧
    Splitting.LagrangianIn B (W ⊓ joint a b c d) (joint a b c d) := by
  let K := Submodule.span F {u, v}
  have huK : u ∈ K := Submodule.subset_span (by simp)
  have hvK : v ∈ K := Submodule.subset_span (by simp)
  have hKW : K ≤ W := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hu.1
    · have : x = v := Set.mem_singleton_iff.mp hx
      simpa [this] using hv.1
  have hKS : K ≤ joint a b c d := by
    apply Submodule.span_le.mpr
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Submodule.mem_sup_left hu.2, Submodule.mem_sup_right hv.2⟩
  have hmax : joint a b c d ⊓ B.orthogonal K ≤ K := by
    intro x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx.1
    have hup : B u p = 0 := by
      simpa [map_add, (cross B a b c d h hu.2 hq).1] using hx.2 u huK
    have hvq : B v q = 0 := by
      simpa [map_add, (cross B a b c d h hp hv.2).2] using hx.2 v hvK
    have hpK : p ∈ K := (Submodule.span_le.mpr (by simpa using huK))
      (Planes.orthogonal_line B a b h.first hu.2 hp hu0 hup)
    have hqK : q ∈ K := (Submodule.span_le.mpr (by simpa using hvK))
      (Planes.orthogonal_line B c d h.second hv.2 hq hv0 hvq)
    exact K.add_mem hpK hqK
  have hself : joint a b c d ⊓ B.orthogonal K = K := by
    apply le_antisymm hmax
    exact le_inf hKS (fun x hx y hy => hW (hKW hx) y (hKW hy))
  have heq : W ⊓ joint a b c d = K := by
    apply le_antisymm
    · intro x hx
      exact hmax ⟨hx.2, fun y hy => hW hx.1 y (hKW hy)⟩
    · exact le_inf hKW hKS
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ⟨hKS, hself⟩

private theorem bit_surjective : Function.Surjective bit := by decide

/-- The chart ranges over the joint plane sum, proved from span membership. -/
theorem chart_range (a b c d x : V) :
    x ∈ joint a b c d ↔ ∃ q : Local.V, chart a b c d q = x := by
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hp
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hq
    obtain ⟨α, rfl⟩ := bit_surjective α
    obtain ⟨β, rfl⟩ := bit_surjective β
    obtain ⟨γ, rfl⟩ := bit_surjective γ
    obtain ⟨δ, rfl⟩ := bit_surjective δ
    refine ⟨(α, γ, β, δ), ?_⟩
    dsimp [chart]
    abel
  · rintro ⟨q, rfl⟩
    have ha : a ∈ joint a b c d := Submodule.mem_sup_left (Submodule.subset_span (by simp))
    have hb : b ∈ joint a b c d := Submodule.mem_sup_left (Submodule.subset_span (by simp))
    have hc : c ∈ joint a b c d := Submodule.mem_sup_right (Submodule.subset_span (by simp))
    have hd : d ∈ joint a b c d := Submodule.mem_sup_right (Submodule.subset_span (by simp))
    exact (joint a b c d).add_mem
      ((joint a b c d).add_mem ((joint a b c d).add_mem
        ((joint a b c d).smul_mem _ ha) ((joint a b c d).smul_mem _ hc))
        ((joint a b c d).smul_mem _ hb)) ((joint a b c d).smul_mem _ hd)

-- The finite pair calculation evaluates a quantified Boolean identity.
set_option maxRecDepth 100000 in
private theorem local_nondegenerate : ∀ q : Local.V,
    (∀ r : Local.V, Local.sp q r = false) → q = 0 := by decide

private theorem local_symm : ∀ q r : Local.V, Local.sp q r = Local.sp r q := by decide

private theorem separating (B : BilinForm F V) (a b c d : V) (h : Frame B a b c d)
    {x : V} (hx : x ∈ joint a b c d)
    (hz : ∀ y ∈ joint a b c d, B x y = 0) : x = 0 := by
  obtain ⟨q, rfl⟩ := (chart_range a b c d x).mp hx
  have hq : q = 0 := by
    apply local_nondegenerate
    intro r
    have hr := hz (chart a b c d r) ((chart_range _ _ _ _ _).mpr ⟨r, rfl⟩)
    rw [LocalChart.chart_form B a b c d h] at hr
    cases hs : Local.sp q r
    · rfl
    · simp [hs, bit] at hr
  rw [hq, LocalChart.chart_zero]

/-- The joint span is a nondegenerate symplectic summand. -/
theorem joint_nondegenerate (B : BilinForm F V) (a b c d : V) (h : Frame B a b c d) :
    (B.restrict (joint a b c d)).Nondegenerate := by
  have hsym {x y : V} (hx : x ∈ joint a b c d) (hy : y ∈ joint a b c d) : B x y = B y x := by
    obtain ⟨q, rfl⟩ := (chart_range a b c d x).mp hx
    obtain ⟨r, rfl⟩ := (chart_range a b c d y).mp hy
    rw [LocalChart.chart_form B a b c d h, LocalChart.chart_form B a b c d h, local_symm]
  constructor
  · intro x hx
    apply Subtype.ext
    exact separating B a b c d h x.property (fun y hy => hx ⟨y, hy⟩)
  · intro x hx
    apply Subtype.ext
    apply separating B a b c d h x.property
    intro y hy
    rw [hsym x.property hy]
    exact hx ⟨y, hy⟩

private def cnotCoordinates (q : Local.V) : Local.V :=
  (q.1 ^^ q.2.1, q.2.1, q.2.2.1, q.2.2.1 ^^ q.2.2.2)

private theorem cnotCoordinates_involutive : ∀ q : Local.V,
    cnotCoordinates (cnotCoordinates q) = q := by decide

private theorem chart_cnot (a b c d : V) (q : Local.V) :
    chart a (b + d) (c + a) d q = chart a b c d (cnotCoordinates q) := by
  simp only [chart, cnotCoordinates, LocalChart.bit_xor, smul_add, add_smul]
  abel

/-- A CNOT preserves the joint subspace of its two endpoint planes. -/
theorem cnot_joint (a b c d : V) : joint a (b + d) (c + a) d = joint a b c d := by
  ext x
  rw [chart_range, chart_range]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨cnotCoordinates q, (chart_cnot a b c d q).symm.trans hq⟩
  · rintro ⟨q, hq⟩
    refine ⟨cnotCoordinates q, ?_⟩
    rw [chart_cnot, cnotCoordinates_involutive]
    exact hq

end CliffordSynthesis.PairGeometry
