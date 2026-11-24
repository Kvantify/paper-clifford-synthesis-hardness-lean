/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PairInventory

/-!
# Pair Origins

Every intact pair can be traced to its creating D gate. Between its
creation and its return no paid gate touches either endpoint, so its original
two-dimensional visible span is preserved.
-/

@[expose] public section

namespace CliffordSynthesis.PairOrigins

open LinearMap (BilinForm)
open Planes (F plane)
open SymplecticCircuit (Rows IsSymplectic applyGate run)
open PairInventory (event step evolve)
open Observation (visible)
open WireGeometry (wire joint)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

def Avoids (g : Circuit.Gate n) (i j : Fin n) : Prop :=
  Circuit.Gate.casesOn g (fun _ => True) (fun _ => True)
    (fun c t _ => i ≠ c ∧ i ≠ t ∧ j ≠ c ∧ j ≠ t)

def DeathAt (W : Submodule F V) (a : Rows n V) (g : Circuit.Gate n) (i j : Fin n) : Prop :=
  Circuit.Gate.casesOn g (fun _ => False) (fun _ => False)
    (fun c t _ => event W a c t = .D ∧ ((i = c ∧ j = t) ∨ (i = t ∧ j = c)))

def HasOrigin (W : Submodule F V) (a : Rows n V) (gs : List (Circuit.Gate n)) (i j : Fin n) : Prop :=
  ∃ pre g post, gs = pre ++ g :: post ∧ DeathAt W (run pre a) g i j ∧
    ∀ h ∈ post, Avoids h i j

omit [Module F V] in
theorem run_append (gs hs : List (Circuit.Gate n)) (a : Rows n V) :
    run (gs ++ hs) a = run hs (run gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih (applyGate g a)

/-- A pair after a gate is either a surviving untouched pair or was just
created by a D gate on those same two physical wires. -/
theorem step_origin (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (g : Circuit.Gate n) (i j : Fin n) (h : (step W a m g).mate i = some j) :
    (m.mate i = some j ∧ Avoids g i j) ∨ DeathAt W a g i j := by
  cases g with
  | H q => exact Or.inl ⟨h, trivial⟩
  | S q => exact Or.inl ⟨h, trivial⟩
  | CX c t hct =>
    change (PairInventory.paidStep W a m c t hct).mate i = some j at h
    unfold PairInventory.paidStep at h
    split_ifs at h with he
    · rw [Matching.insert_mate] at h
      split_ifs at h with hic hit
      · right
        exact ⟨he, Or.inl ⟨hic, (Option.some.inj h).symm⟩⟩
      · right
        exact ⟨he, Or.inr ⟨hit, (Option.some.inj h).symm⟩⟩
      · obtain ⟨hm, hic, hit, hjc, hjt⟩ := Matching.erase_some m c t i j h
        exact Or.inl ⟨hm, hic, hit, hjc, hjt⟩
    · obtain ⟨hm, hic, hit, hjc, hjt⟩ := Matching.erase_some m c t i j h
      exact Or.inl ⟨hm, hic, hit, hjc, hjt⟩

theorem evolve_origin (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (m : Matching.State n) (i j : Fin n) (h : (evolve W gs a m).mate i = some j) :
    (m.mate i = some j ∧ ∀ g ∈ gs, Avoids g i j) ∨ HasOrigin W a gs i j := by
  induction gs generalizing a m with
  | nil => exact Or.inl ⟨h, by simp⟩
  | cons g gs ih =>
    have ht := ih (applyGate g a) (step W a m g) h
    rcases ht with ⟨hm, havoid⟩ | ⟨pre, death, post, heq, hd, hpost⟩
    · rcases step_origin W a m g i j hm with ⟨hm, hg⟩ | hd
      · left
        refine ⟨hm, ?_⟩
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hg
        · exact havoid k hk
      · exact Or.inr ⟨[], g, gs, rfl, hd, havoid⟩
    · right
      refine ⟨g :: pre, death, post, ?_, hd, hpost⟩
      simp [heq]

theorem origin_from_empty (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (i j : Fin n) (h : (evolve W gs a (Matching.empty n)).mate i = some j) :
    HasOrigin W a gs i j := by
  rcases evolve_origin W gs a (Matching.empty n) i j h with ⟨h, _⟩ | h
  · contradiction
  · exact h

theorem avoids_wires (g : Circuit.Gate n) (a : Rows n V) (i j : Fin n) (h : Avoids g i j) :
    wire (applyGate g a) i = wire a i ∧ wire (applyGate g a) j = wire a j := by
  cases g with
  | H q => exact ⟨WireGeometry.H_wire a q i, WireGeometry.H_wire a q j⟩
  | S q => exact ⟨WireGeometry.S_wire a q i, WireGeometry.S_wire a q j⟩
  | CX c t _ => exact ⟨WireGeometry.CX_wire a c t i h.1 h.2.1,
      WireGeometry.CX_wire a c t j h.2.2.1 h.2.2.2⟩

theorem run_avoids_wires (gs : List (Circuit.Gate n)) (a : Rows n V) (i j : Fin n)
    (h : ∀ g ∈ gs, Avoids g i j) : wire (run gs a) i = wire a i ∧ wire (run gs a) j = wire a j := by
  induction gs generalizing a with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih =>
    have hg := avoids_wires g a i j (h g (by simp))
    have ht := ih (applyGate g a) (fun k hk => h k (List.mem_cons_of_mem g hk))
    exact ⟨ht.1.trans hg.1, ht.2.trans hg.2⟩

theorem death_joint (W : Submodule F V) (a : Rows n V) (g : Circuit.Gate n) (i j : Fin n)
    (h : DeathAt W a g i j) : i ≠ j ∧ joint (applyGate g a) i j = joint a i j := by
  cases g with
  | H q => contradiction
  | S q => contradiction
  | CX c t hct =>
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hct, WireGeometry.CX_joint a _ _ hct⟩
    · refine ⟨Ne.symm hct, ?_⟩
      simpa only [joint, sup_comm, applyGate] using WireGeometry.CX_joint a _ _ hct

theorem death_visible (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (g : Circuit.Gate n) (i j : Fin n)
    (h : DeathAt W a g i j) :
    ∃ u v, visible W a i = some u ∧ visible W a j = some v := by
  cases g with
  | H q => contradiction
  | S q => contradiction
  | CX c t hct =>
    have hb := PairInventory.before_two B W hW a ha c t hct (by rw [h.1]; rfl)
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hb.1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hb.2
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨u, v, hu, hv⟩
    · exact ⟨v, u, hv, hu⟩

/-- The current intersection of any intact pair is exactly the span of its
two visible vectors immediately before its creating D gate. -/
theorem origin_span (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (i j : Fin n) (h : (evolve W gs a (Matching.empty n)).mate i = some j) :
    ∃ pre g post u v, gs = pre ++ g :: post ∧ DeathAt W (run pre a) g i j ∧
      visible W (run pre a) i = some u ∧ visible W (run pre a) j = some v ∧
      W ⊓ joint (run gs a) i j = plane u v ∧ pre.length < gs.length := by
  obtain ⟨pre, g, post, heq, hd, hpost⟩ := origin_from_empty W gs a i j h
  have hpre := SymplecticCircuit.run_symplectic B pre a ha
  obtain ⟨u, v, hu, hv⟩ := death_visible B W hW _ hpre g i j hd
  obtain ⟨hij, hjoint⟩ := death_joint W (run pre a) g i j hd
  have hspan := (WireGeometry.visible_pair_lagrangian B W hW _ hpre i j hij u v hu hv).1
  refine ⟨pre, g, post, u, v, heq, hd, hu, hv, ?_, ?_⟩
  · have hw := run_avoids_wires post (applyGate g (run pre a)) i j hpost
    have hs : W ⊓ joint (applyGate g (run pre a)) i j = plane u v := by
      rw [hjoint]
      exact hspan
    rw [heq, run_append]
    change W ⊓ joint (run post (applyGate g (run pre a))) i j = _
    simpa only [joint, hw.1, hw.2] using hs
  · simp only [heq, List.length_append, List.length_cons]
    omega

/-- Returned visible vectors of an intact pair lie in its earlier visible span. -/
theorem return_span (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (c t : Fin n) (hct : c ≠ t) (hm : (evolve W gs a (Matching.empty n)).mate c = some t)
    (p q : V) (hp : visible W (SymplecticCircuit.CX c t (run gs a)) c = some p)
    (hq : visible W (SymplecticCircuit.CX c t (run gs a)) t = some q) :
    ∃ pre g post u v, gs = pre ++ g :: post ∧
      visible W (run pre a) c = some u ∧ visible W (run pre a) t = some v ∧
      p ∈ plane u v ∧ q ∈ plane u v ∧ pre.length < gs.length := by
  obtain ⟨pre, g, post, u, v, heq, _, hu, hv, hs, hlt⟩ := origin_span B W hW gs a ha c t hm
  have hafter := SymplecticCircuit.CX_symplectic B _ (SymplecticCircuit.run_symplectic B gs a ha) c t hct
  have hp' := (WireGeometry.visible_spec B W hW _ hafter c p).mp hp
  have hq' := (WireGeometry.visible_spec B W hW _ hafter t q).mp hq
  have hs' : W ⊓ joint (SymplecticCircuit.CX c t (run gs a)) c t = plane u v := by
    rw [WireGeometry.CX_joint _ c t hct, hs]
  refine ⟨pre, g, post, u, v, heq, hu, hv, ?_, ?_, hlt⟩
  · rw [← hs']
    exact ⟨hp'.2.1, Submodule.mem_sup_left hp'.2.2⟩
  · rw [← hs']
    exact ⟨hq'.2.1, Submodule.mem_sup_right hq'.2.2⟩

end CliffordSynthesis.PairOrigins
