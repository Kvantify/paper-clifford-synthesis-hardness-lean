/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.WireGeometry
public import CliffordSynthesis.Matching

/-!
# Pair Inventory

An untouched-pair inventory constructed and maintained by the actual
circuit. Validity includes the hidden-wire and Lagrangian invariants.
-/

@[expose] public section

namespace CliffordSynthesis.PairInventory

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic H S CX applyGate)
open Observation (visible present signature)
open WireGeometry (wire joint)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

def Valid (B : BilinForm F V) (W : Submodule F V) (a : Rows n V) (m : Matching.State n) : Prop :=
  ∀ i j, m.mate i = some j → visible W a i = none ∧
    Splitting.LagrangianIn B (W ⊓ joint a i j) (joint a i j)

theorem empty_valid (B : BilinForm F V) (W : Submodule F V) (a : Rows n V) :
    Valid B W a (Matching.empty n) := by
  intro i j h
  contradiction

theorem visible_unpaired (B : BilinForm F V) (W : Submodule F V) (a : Rows n V)
    (m : Matching.State n) (hm : Valid B W a m) (i : Fin n)
    (hi : (visible W a i).isSome = true) : m.mate i = none := by
  cases he : m.mate i with
  | none => rfl
  | some j => simp [(hm i j he).1] at hi

theorem H_valid (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (q : Fin n) : Valid B W (H q a) m := by
  intro i j hij
  simpa only [Observation.hadamard_visible B W hW a ha, joint, WireGeometry.H_wire] using hm i j hij

theorem S_valid (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (q : Fin n) : Valid B W (S q a) m := by
  intro i j hij
  simpa only [Observation.phase_visible B W hW a ha, joint, WireGeometry.S_wire] using hm i j hij

theorem erase_valid (B : BilinForm F V) (W : Submodule F V)
    (a : Rows n V) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) : Valid B W (CX c t a) (Matching.erase m c t) := by
  intro i j hij
  obtain ⟨hij, hic, hit, hjc, hjt⟩ := Matching.erase_some m c t i j hij
  simpa only [Observation.cnot_untouched W a c t i hic hit, joint,
    WireGeometry.CX_wire a c t i hic hit, WireGeometry.CX_wire a c t j hjc hjt] using hm i j hij

noncomputable def event (W : Submodule F V) (a : Rows n V) (c t : Fin n) : Ledger.Event :=
  CircuitLedger.classify (signature W a (CX c t a) c t)

private theorem present_two {α : Type*} (o p : Option α) :
    present o + present p = 2 ↔ o.isSome = true ∧ p.isSome = true := by
  cases o <;> cases p <;> simp [present]

private theorem present_zero {α : Type*} (o p : Option α) :
    present o + present p = 0 ↔ o = none ∧ p = none := by
  cases o <;> cases p <;> simp [present]

theorem before_two (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t)
    (he : (event W a c t).before = 2) :
    (visible W a c).isSome = true ∧ (visible W a t).isSome = true := by
  apply (present_two _ _).mp
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  exact hs.1.symm.trans he

theorem after_two (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t)
    (he : (event W a c t).after = 2) :
    (visible W (CX c t a) c).isSome = true ∧ (visible W (CX c t a) t).isSome = true := by
  apply (present_two _ _).mp
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  exact hs.2.1.symm.trans he

theorem before_zero (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t)
    (he : (event W a c t).before = 0) : visible W a c = none ∧ visible W a t = none := by
  apply (present_zero _ _).mp
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  exact hs.1.symm.trans he

theorem after_zero (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t)
    (he : (event W a c t).after = 0) :
    visible W (CX c t a) c = none ∧ visible W (CX c t a) t = none := by
  apply (present_zero _ _).mp
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  exact hs.2.1.symm.trans he

/-- A U gate touching a paired control must return with exactly its partner. -/
theorem U_partner (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t j : Fin n) (hct : c ≠ t) (he : event W a c t = .U) (hcj : m.mate c = some j) :
    j = t := by
  by_contra hjt
  have hbefore := before_zero B W hW a ha c t hct (by rw [he]; rfl)
  have hafter := after_two B W hW a ha c t hct (by rw [he]; rfl)
  have hnone := WireGeometry.no_cross_return B W hW a ha c j t hct hjt
    (hm c j hcj).2 hbefore.1 hbefore.2
  simp [hnone.1] at hafter

theorem U_partner_right (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t j : Fin n) (hct : c ≠ t) (he : event W a c t = .U) (htj : m.mate t = some j) :
    j = c := by
  by_contra hjc
  have hbefore := before_zero B W hW a ha c t hct (by rw [he]; rfl)
  have hafter := after_two B W hW a ha c t hct (by rw [he]; rfl)
  have hz := WireGeometry.cross_joint_zero B W hW a ha t j c (Ne.symm hct) hjc
    (hm t j htj).2 hbefore.2 hbefore.1
  have hz' : W ⊓ joint a c t = ⊥ := by simpa [joint, sup_comm] using hz
  have hnone := WireGeometry.CX_hidden_of_joint B W hW a ha c t hct hz'
  simp [hnone.1] at hafter

/-- Every U is exactly an untouched-pair return or consumes two unpaired
hidden wires. This is derived from the physical circuit and geometric invariant. -/
theorem U_dichotomy (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .U) :
    (m.mate c = some t ∧ m.mate t = some c) ∨ (m.mate c = none ∧ m.mate t = none) := by
  cases hc : m.mate c with
  | some j =>
    have hj := U_partner B W hW a ha m hm c t j hct he hc
    subst j
    exact Or.inl ⟨rfl, m.symmetric c t hc⟩
  | none =>
    right
    refine ⟨rfl, ?_⟩
    cases ht : m.mate t with
    | none => rfl
    | some j =>
      have hj := U_partner_right B W hW a ha m hm c t j hct he ht
      subst j
      have hh := m.symmetric t c ht
      rw [hc] at hh
      contradiction

/-- A type P gate cannot involve either endpoint of a listed pair. Both of
its hidden participants must therefore belong to the marked set. -/
theorem P_unpaired (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .P) :
    m.mate c = none ∧ m.mate t = none := by
  have hb := before_zero B W hW a ha c t hct (by rw [he]; rfl)
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  have hf : present (visible W (CX c t a) c) + present (visible W (CX c t a) t) = 1 :=
    hs.2.1.symm.trans (by change (event W a c t).after = 1; rw [he]; rfl)
  have hnotpair : ¬ Splitting.LagrangianIn B (W ⊓ joint a c t) (joint a c t) := by
    intro hlag
    have hlag' : Splitting.LagrangianIn B (W ⊓ joint (CX c t a) c t)
        (joint (CX c t a) c t) := by simpa only [WireGeometry.CX_joint a c t hct] using hlag
    have ha' := SymplecticCircuit.CX_symplectic B a ha c t hct
    have h₁ := WireGeometry.lagrangian_visible_partner B W hW (CX c t a) ha' c t hct hlag'
    have h₂ := WireGeometry.lagrangian_visible_partner B W hW (CX c t a) ha' t c
      (Ne.symm hct) (by simpa only [joint, sup_comm] using hlag')
    cases hc : visible W (CX c t a) c <;> cases ht : visible W (CX c t a) t <;>
      simp [hc, ht, present] at hf h₁ h₂
  constructor
  · cases hc : m.mate c with
    | none => rfl
    | some j =>
      by_cases hjt : j = t
      · subst j; exact False.elim (hnotpair (hm c t hc).2)
      · have hz := WireGeometry.no_cross_return B W hW a ha c j t hct hjt
          (hm c j hc).2 hb.1 hb.2
        simp [hz.1, hz.2, present] at hf
  · cases ht : m.mate t with
    | none => rfl
    | some j =>
      by_cases hjc : j = c
      · subst j
        exact False.elim (hnotpair (by simpa only [joint, sup_comm] using (hm t c ht).2))
      · have hz := WireGeometry.cross_joint_zero B W hW a ha t j c (Ne.symm hct) hjc
          (hm t j ht).2 hb.2 hb.1
        have hz' : W ⊓ joint a c t = ⊥ := by simpa only [joint, sup_comm] using hz
        have hn := WireGeometry.CX_hidden_of_joint B W hW a ha c t hct hz'
        simp [hn.1, hn.2, present] at hf

private theorem insert_valid (B : BilinForm F V) (W : Submodule F V)
    (a : Rows n V) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (hc : m.mate c = none) (ht : m.mate t = none)
    (hvc : visible W a c = none) (hvt : visible W a t = none)
    (hlag : Splitting.LagrangianIn B (W ⊓ joint a c t) (joint a c t)) :
    Valid B W a (Matching.insert m c t hct hc ht) := by
  intro i j hij
  rw [Matching.insert_mate] at hij
  split_ifs at hij with hic hit
  · have h : t = j := Option.some.inj hij
    subst i; subst j
    exact ⟨hvc, hlag⟩
  · have h : c = j := Option.some.inj hij
    subst i; subst j
    exact ⟨hvt, by simpa [joint, sup_comm] using hlag⟩
  · exact hm i j hij

noncomputable def paidStep (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) : Matching.State n :=
  if event W a c t = .D then
    Matching.insert (Matching.erase m c t) c t hct (Matching.erase_left m c t) (Matching.erase_right m c t)
  else Matching.erase m c t

theorem paidStep_valid (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) : Valid B W (CX c t a) (paidStep W a m c t hct) := by
  unfold paidStep
  split_ifs with he
  · have hb := before_two B W hW a ha c t hct (by rw [he]; rfl)
    have hf := after_zero B W hW a ha c t hct (by rw [he]; rfl)
    apply insert_valid B W _ _ (erase_valid B W a m hm c t) c t hct _ _ hf.1 hf.2
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hb.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hb.2
    rw [WireGeometry.CX_joint a c t hct]
    exact (WireGeometry.visible_pair_lagrangian B W hW a ha c t hct u v hu hv).2
  · exact erase_valid B W a m hm c t

noncomputable def step (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (g : Circuit.Gate n) : Matching.State n :=
  Circuit.Gate.casesOn g (fun _ => m) (fun _ => m) (fun c t hct => paidStep W a m c t hct)

theorem step_valid (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (g : Circuit.Gate n) : Valid B W (applyGate g a) (step W a m g) := by
  cases g with
  | H q => exact H_valid B W hW a ha m hm q
  | S q => exact S_valid B W hW a ha m hm q
  | CX c t hct => exact paidStep_valid B W hW a ha m hm c t hct

noncomputable def evolve (W : Submodule F V) (gs : List (Circuit.Gate n)) :
    Rows n V → Matching.State n → Matching.State n :=
  gs.rec (fun _ m => m) (fun g _ tail a m => tail (applyGate g a) (step W a m g))

theorem evolve_valid (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (m : Matching.State n) (hm : Valid B W a m) :
    Valid B W (SymplecticCircuit.run gs a) (evolve W gs a m) := by
  induction gs generalizing a m with
  | nil => exact hm
  | cons g gs ih =>
    exact ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
      (step W a m g) (step_valid B W hW a ha m hm g)

/-- Every actual circuit prefix has the constructed geometric pair inventory. -/
theorem actual_inventory (gs : List (Circuit.Gate n)) :
    Valid (StandardSpace.form n) (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n)))
      (evolve (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n)) := by
  rw [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity]
  exact evolve_valid _ _ (StandardSpace.initialW_isotropic n) gs _
    (StandardSpace.standard_symplectic n) _ (empty_valid _ _ _)

end CliffordSynthesis.PairInventory
