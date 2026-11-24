/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GadgetReplacement
public import GridHardness.OrbitSplicing
public import Mathlib.Data.Fintype.Sum

/-!
# Mandatory Arc Subdivision

Subdivision of an actual directed arc by a nonempty path of fresh vertices.
The degree conditions in `Mandatory` force the arc in every Hamiltonian cycle;
no cycle traversal is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.MandatoryArcSubdivision
variable {V : Type*}

/-- Either the source has only the named outgoing arc, or the target has
only the named incoming arc. The arc itself must belong to the ambient graph. -/
def Mandatory (D : V → V → Prop) (s t : V) : Prop :=
  D s t ∧ ((∀ v, D s v → v = t) ∨ (∀ u, D u t → u = s))

/-- `n+1` fresh vertices replace the named arc. All other ambient arcs remain. -/
abbrev Vertex (V : Type*) (n : Nat) := V ⊕ Fin (n+1)

def Adj (D : V → V → Prop) (s t : V) (n : Nat) : Vertex V n → Vertex V n → Prop
  | .inl u, .inl v => D u v ∧ ¬ (u = s ∧ v = t)
  | .inl u, .inr j => u = s ∧ j = 0
  | .inr i, .inl v => i = Fin.last n ∧ v = t
  | .inr i, .inr j => j.val = i.val + 1

@[simp] theorem vertex_count [Fintype V] (n : Nat) :
    Fintype.card (Vertex V n) = Fintype.card V + (n+1) := by simp [Vertex]

theorem mandatory_step (D : V → V → Prop) (s t : V) (h : Mandatory D s t)
    (next : Equiv.Perm V) (ha : ∀ v, D v (next v)) : next s = t := by
  rcases h.2 with hout | hin
  · exact hout _ (ha s)
  · obtain ⟨u,hu⟩ := next.surjective t
    have hs : u = s := hin u (hu ▸ ha u)
    simpa only [hs] using hu

section Expansion
variable [DecidableEq V]

def expand (s t : V) (n : Nat) (next : V → V) : Vertex V n → Vertex V n
  | .inl v => if v = s then .inr 0 else .inl (next v)
  | .inr i => if h : i.val < n then .inr ⟨i.val+1,by omega⟩ else .inl t

@[simp] theorem expand_source (s t : V) (n : Nat) (next : V → V) :
    expand s t n next (.inl s) = .inr 0 := by simp [expand]

@[simp] theorem expand_fresh (s t : V) (n : Nat) (next : V → V) (i : Fin n) :
    expand s t n next (.inr i.castSucc) = .inr i.succ := by
  simp [expand,i.isLt]
  exact Fin.ext rfl

@[simp] theorem expand_last (s t : V) (n : Nat) (next : V → V) :
    expand s t n next (.inr (Fin.last n)) = .inl t := by simp [expand]

theorem fresh_from_first (s t : V) (n : Nat) (next : V → V) (i : Fin (n +1)) :
    StepReach (expand s t n next) (.inr 0) (.inr i) := by
  induction i using Fin.induction with
  | zero => exact StepReach.refl _ _
  | succ i ih => exact ih.trans ⟨1,expand_fresh s t n next i⟩

theorem fresh_to_target (s t : V) (n : Nat) (next : V → V) (i : Fin (n +1)) :
    StepReach (expand s t n next) (.inr i) (.inl t) := by
  induction i using Fin.reverseInduction with
  | last => exact ⟨1,expand_last s t n next⟩
  | cast i ih => exact (show StepReach (expand s t n next) (.inr i.castSucc) (.inr i.succ) from
      ⟨1,expand_fresh s t n next i⟩).trans ih

theorem expand_oneOrbit (s t : V) (n : Nat) (next : V → V)
    (ho : OneOrbit next) (hst : next s = t) : OneOrbit (expand s t n next) := by
  apply ho.expand Sum.inl
  · intro v
    by_cases hv : v = s
    · subst v
      rw [hst]
      exact (show StepReach (expand s t n next) (.inl s) (.inr 0) from ⟨1,expand_source s t n next⟩).trans
        (fresh_to_target s t n next 0)
    · exact ⟨1,by simp [expand,hv]⟩
  · intro v
    cases v with
    | inl v => exact ⟨v,StepReach.refl _ _⟩
    | inr i => exact ⟨t,fresh_to_target s t n next i⟩
  · intro v
    cases v with
    | inl v => exact ⟨v,StepReach.refl _ _⟩
    | inr i => exact ⟨s,(show StepReach (expand s t n next) (.inl s) (.inr 0) from
        ⟨1,expand_source s t n next⟩).trans (fresh_from_first s t n next i)⟩

theorem expand_adj (D : V → V → Prop) (s t : V) (n : Nat) (next : V → V)
    (ha : ∀ v, D v (next v)) (v : Vertex V n) : Adj D s t n v (expand s t n next v) := by
  cases v with
  | inl v =>
    by_cases hv : v = s
    · subst v
      simp [expand,Adj]
    · simp only [expand,ite_eq_right hv,Adj]
      exact ⟨ha v,fun h => hv h.1⟩
  | inr i =>
    by_cases hi : i.val < n
    · simp [expand,hi,Adj]
    · simp only [expand,dite_eq_right hi,Adj]
      exact ⟨Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega),trivial⟩

end Expansion

/-- Forward preservation follows from the structural degree condition. -/
theorem hamiltonian_expand [Finite V] (D : V → V → Prop) (s t : V) (n : Nat)
    (h : Mandatory D s t) : PathCover.Hamiltonian D → PathCover.Hamiltonian (Adj D s t n) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  rintro ⟨next,ho,ha⟩
  have he := expand_oneOrbit s t n next ho (mandatory_step D s t h next ha)
  exact ⟨Equiv.ofBijective _ he.bijective,he,expand_adj D s t n next ha⟩

/-- Contract all fresh vertices onto the named source. -/
def project (s : V) (n : Nat) : Vertex V n → V
  | .inl v => v
  | .inr _ => s

section Contraction
variable [DecidableEq V]

def contract (s t : V) (n : Nat) (step : Vertex V n → Vertex V n) (v : V) : V :=
  if v = s then t else project s n (step (.inl v))

@[simp] theorem contract_source (s t : V) (n : Nat) (step : Vertex V n → Vertex V n) :
    contract s t n step s = t := by simp [contract]

theorem step_projects (D : V → V → Prop) (s t : V) (n : Nat)
    (step : Equiv.Perm (Vertex V n)) (ha : ∀ v, Adj D s t n v (step v)) (w : Vertex V n) :
    project s n (step w) = project s n w ∨
      project s n (step w) = contract s t n step (project s n w) := by
  have hs : step (.inl s) = .inr 0 := by
    obtain ⟨v,hv⟩ := step.surjective (.inr 0)
    have hh := ha v
    rw [hv] at hh
    cases v with
    | inl v =>
      obtain ⟨rfl,_⟩ := hh
      exact hv
    | inr i =>
      change (0 : Nat) = i.val+1 at hh
      omega
  cases w with
  | inl v =>
    by_cases hv : v = s
    · subst v
      rw [hs]
      exact Or.inl rfl
    · exact Or.inr (by simp [contract,hv,project])
  | inr i =>
    have hh := ha (.inr i)
    generalize he : step (.inr i) = z at hh ⊢
    cases z with
    | inl v =>
      apply Or.inr
      change v = contract s t n step s
      rw [contract_source]
      exact hh.2
    | inr j => exact Or.inl rfl

theorem contract_adj (D : V → V → Prop) (s t : V) (n : Nat) (hst : D s t)
    (step : Equiv.Perm (Vertex V n)) (ha : ∀ v, Adj D s t n v (step v)) (v : V) :
    D v (contract s t n step v) := by
  by_cases hv : v = s
  · subst v
    simpa only [contract_source] using hst
  · simp only [contract,ite_eq_right hv]
    have hh := ha (.inl v)
    generalize he : step (.inl v) = z at hh ⊢
    cases z with
    | inl u => exact hh.1
    | inr i => exact False.elim (hv hh.1)

end Contraction

/-- Backward preservation needs only that the named arc exists. -/
theorem hamiltonian_contract [Finite V] (D : V → V → Prop) (s t : V) (n : Nat)
    (hst : D s t) : PathCover.Hamiltonian (Adj D s t n) → PathCover.Hamiltonian D := by
  classical
  rintro ⟨step,ho,ha⟩
  have hc := ho.project (project s n) (fun v => ⟨.inl v,rfl⟩) (step_projects D s t n step ha)
  exact ⟨Equiv.ofBijective _ hc.bijective,hc,contract_adj D s t n hst step ha⟩

/-- Subdividing a structurally mandatory arc by any positive number of fresh
vertices preserves the existence of an actual global Hamiltonian cycle. -/
theorem hamiltonian_iff [Finite V] (D : V → V → Prop) (s t : V) (n : Nat)
    (h : Mandatory D s t) : PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (Adj D s t n) :=
  ⟨hamiltonian_expand D s t n h,hamiltonian_contract D s t n h.1⟩

theorem hamiltonian_iff_unique_outgoing [Finite V] (D : V → V → Prop) (s t : V) (n : Nat)
    (hst : D s t) (hout : ∀ v, D s v → v = t) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (Adj D s t n) :=
  hamiltonian_iff D s t n ⟨hst,Or.inl hout⟩

theorem hamiltonian_iff_unique_incoming [Finite V] (D : V → V → Prop) (s t : V) (n : Nat)
    (hst : D s t) (hin : ∀ u, D u t → u = s) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (Adj D s t n) :=
  hamiltonian_iff D s t n ⟨hst,Or.inr hin⟩

end GridHardness.MandatoryArcSubdivision
