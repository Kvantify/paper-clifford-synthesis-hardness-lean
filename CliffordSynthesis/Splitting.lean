/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic

/-!
# Splitting

Lagrangian splitting and the obstruction to cross-pair returns.
These results hold over any field and use Mathlib's bilinear forms and
subspaces directly. No splitting or inventory fact is assumed.
-/

@[expose] public section

namespace CliffordSynthesis.Splitting

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Isotropy in the usual bilinear-form sense. -/
def Isotropic (B : BilinForm K V) (W : Submodule K V) : Prop :=
  W ≤ B.orthogonal W

/-- Self-orthogonality inside a specified symplectic summand. -/
def LagrangianIn (B : BilinForm K V) (W S : Submodule K V) : Prop :=
  W ≤ S ∧ S ⊓ B.orthogonal W = W

/-- The S component of a vector of W is again in W. -/
theorem component_mem (B : BilinForm K V) (W S : Submodule K V)
    (hW : Isotropic B W) (hWS : LagrangianIn B (W ⊓ S) S)
    {s t : V} (hs : s ∈ S) (ht : t ∈ B.orthogonal S) (hw : s + t ∈ W) :
    s ∈ W ∧ t ∈ W := by
  have hsW : s ∈ W := by
    have h : s ∈ S ⊓ B.orthogonal (W ⊓ S) := by
      refine ⟨hs, ?_⟩
      intro u hu
      have hzero := hW hw u hu.1
      simpa only [map_add, ht u hu.2, add_zero] using hzero
    rw [hWS.2] at h
    exact h.1
  exact ⟨hsW, by simpa using W.sub_mem hw hsW⟩

/-- The Lagrangian decomposition lemma, including directness of the sum. -/
theorem lagrangian_splitting [FiniteDimensional K V] (B : BilinForm K V) (W S : Submodule K V)
    (hB : B.IsRefl) (hW : Isotropic B W)
    (hS : (B.restrict S).Nondegenerate)
    (hWS : LagrangianIn B (W ⊓ S) S) :
    W = (W ⊓ S) ⊔ (W ⊓ B.orthogonal S) ∧
    Disjoint (W ⊓ S) (W ⊓ B.orthogonal S) := by
  have hc := B.isCompl_orthogonal_of_restrict_nondegenerate hB hS
  constructor
  · apply le_antisymm
    · intro w hw
      obtain ⟨s, t, hs, ht, rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
      obtain ⟨hsW, htW⟩ := component_mem B W S hW hWS hs ht hw
      exact Submodule.mem_sup.mpr ⟨s, ⟨hsW, hs⟩, t, ⟨htW, ht⟩, rfl⟩
    · exact sup_le inf_le_left inf_le_left
  · exact hc.disjoint.mono inf_le_right inf_le_right

/-- Hidden endpoints in an untouched summand and its complement have no
visible joint vector. This is the geometric step excluding a cross-pair U
return in the hidden-pair inventory argument. -/
theorem no_cross_pair (B : BilinForm K V) (W S P Q : Submodule K V)
    (hW : Isotropic B W) (hWS : LagrangianIn B (W ⊓ S) S)
    (hP : P ≤ S) (hQ : Q ≤ B.orthogonal S)
    (hiddenP : W ⊓ P = ⊥) (hiddenQ : W ⊓ Q = ⊥) :
    W ⊓ (P ⊔ Q) = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  obtain ⟨p, hp, q, hq, heq⟩ := Submodule.mem_sup.mp hw.2
  have hsum : p + q ∈ W := heq ▸ hw.1
  obtain ⟨hpW, hqW⟩ := component_mem B W S hW hWS (hP hp) (hQ hq) hsum
  have hp0 : p = 0 := by
    have : p ∈ W ⊓ P := ⟨hpW, hp⟩
    simpa [hiddenP] using this
  have hq0 : q = 0 := by
    have : q ∈ W ⊓ Q := ⟨hqW, hq⟩
    simpa [hiddenQ] using this
  simpa [hp0, hq0] using heq.symm

end CliffordSynthesis.Splitting
