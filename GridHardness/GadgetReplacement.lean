/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrbitPathCover

/-!
# Gadget Replacement

A graph-level replacement theorem for explicit disjoint path covers.
The classification premise is separate from graph construction: applications
must prove it from the actual gadget's incident edges and a spanning cycle.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PathCover

/-- Coordinates for a partition into nonempty, ordered paths. The equivalence
asserts that every vertex occurs in exactly one of these explicit paths. -/
structure Cover (I W : Type*) where
  size : I → Nat
  equiv : Blocks size ≃ W

namespace Cover

def first {I W : Type*} (c : Cover I W) (i : I) : W := c.equiv (entry c.size i)
def finish {I W : Type*} (c : Cover I W) (i : I) : W := c.equiv (last c.size i)

def conjugate {I W : Type*} (c : Cover I W) (step : Equiv.Perm W) :
    Equiv.Perm (Blocks c.size) := c.equiv.trans (step.trans c.equiv.symm)

theorem conjugate_oneOrbit {I W : Type*} (c : Cover I W) (step : Equiv.Perm W)
    (ho : OneOrbit step) : OneOrbit (c.conjugate step) := by
  apply ho.transport c.equiv.symm
  intro w
  simp [conjugate]

def InternalEdges {I W : Type*} (c : Cover I W) (D : W → W → Prop) : Prop :=
  ∀ (i : I) (j : Fin (c.size i)), D (c.equiv ⟨i, j.castSucc⟩) (c.equiv ⟨i, j.succ⟩)

def Wiring {I W : Type*} (c : Cover I W) (D : W → W → Prop) (i j : I) : Prop :=
  D (c.finish i) (c.first j)

/-- The Hamiltonian successor has this path cover as its internal routes. -/
def FollowedBy {I W : Type*} (c : Cover I W) (step : Equiv.Perm W) : Prop :=
  Follows (c.conjugate step)

theorem contract_adjacent {I W : Type*} (c : Cover I W) (D : W → W → Prop)
    (step : Equiv.Perm W) (hf : c.FollowedBy step) (ha : ∀ w, D w (step w)) :
    ∀ i, c.Wiring D i (contract (c.conjugate step) i) := by
  intro i
  have he := last_maps_to_entry (c.conjugate step).injective hf i
  have hw := congrArg c.equiv he
  simp only [conjugate, Equiv.trans_apply, Equiv.apply_symm_apply] at hw
  change step (c.equiv (last c.size i)) =
    c.equiv (entry c.size (contract (c.conjugate step) i)) at hw
  change D (c.equiv (last c.size i)) (c.equiv (entry c.size _))
  rw [← hw]
  exact ha _

theorem expand_adjacent {I W : Type*} (c : Cover I W) (D : W → W → Prop)
    (hi : c.InternalEdges D) (next : I → I) (ha : ∀ i, c.Wiring D i (next i)) :
    ∀ w, D (c.equiv w) (c.equiv (expand c.size next w)) := by
  rintro ⟨i, j⟩
  cases j using Fin.lastCases with
  | last =>
    change D (c.equiv (last c.size i)) (c.equiv (expand c.size next (last c.size i)))
    rw [expand_last]
    exact ha i
  | cast j =>
    rw [expand_follows c.size next i j]
    exact hi i j

end Cover

/-- Directed Hamiltonicity in successor-permutation form. On an empty type
this is vacuous; reduction sources that reject empty instances also include
their own nonemptiness guard. -/
def Hamiltonian {W : Type*} (D : W → W → Prop) : Prop :=
  ∃ step : Equiv.Perm W, OneOrbit step ∧ ∀ w, D w (step w)

/-- A fixed explicit path cover can be expanded along any Hamiltonian cycle
of its endpoint wiring. All internal graph edges are checked by `hi`. -/
theorem Cover.expand_hamiltonian {I W : Type*} [Finite I]
    (c : Cover I W) (D : W → W → Prop) (hi : c.InternalEdges D)
    (h : Hamiltonian (c.Wiring D)) : Hamiltonian D := by
  obtain ⟨next, ho, ha⟩ := h
  have hx := oneOrbit_expand ho c.size
  let expanded : Equiv.Perm (Blocks c.size) := Equiv.ofBijective _ hx.bijective
  let step : Equiv.Perm W := c.equiv.symm.trans (expanded.trans c.equiv)
  have hs : ∀ v, step (c.equiv v) = c.equiv (expand c.size next v) := by
    intro v
    simp [step, expanded]
  refine ⟨step, hx.transport c.equiv hs, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := c.equiv.surjective w
  rw [hs]
  exact c.expand_adjacent D hi next ha v

/-- Contract an actual Hamiltonian traversal after proving its local route
classification. Injectivity supplies the endpoint-entry condition. -/
theorem Cover.contract_hamiltonian {I W : Type*} [Finite I]
    (c : Cover I W) (D : W → W → Prop) (step : Equiv.Perm W)
    (ho : OneOrbit step) (ha : ∀ w, D w (step w)) (hf : c.FollowedBy step) :
    Hamiltonian (c.Wiring D) := by
  have hc := oneOrbit_contract (c.conjugate_oneOrbit step ho) hf
  exact ⟨Equiv.ofBijective _ hc.bijective, hc, c.contract_adjacent D step hf ha⟩

/-- A finite family of verified path covers gives an exact graph-level
characterization once every Hamiltonian traversal is classified into it. -/
theorem hamiltonian_iff_wiring {S I W : Type*} [Finite I]
    (covers : S → Cover I W) (D : W → W → Prop)
    (hi : ∀ s, (covers s).InternalEdges D)
    (classify : ∀ step : Equiv.Perm W, OneOrbit step → (∀ w, D w (step w)) →
      ∃ s, (covers s).FollowedBy step) :
    Hamiltonian D ↔ ∃ s, Hamiltonian ((covers s).Wiring D) := by
  constructor
  · rintro ⟨step, ho, ha⟩
    obtain ⟨s, hs⟩ := classify step ho ha
    exact ⟨s, (covers s).contract_hamiltonian D step ho ha hs⟩
  · rintro ⟨s, hs⟩
    exact (covers s).expand_hamiltonian D (hi s) hs

/-- Two concrete gadget assemblies are interchangeable when their verified
route families have exactly the same endpoint wiring. This preserves the
single global spanning cycle, rather than merely a cycle cover. -/
theorem replacement_iff {S I W W' : Type*} [Finite I]
    (left : S → Cover I W) (right : S → Cover I W')
    (D : W → W → Prop) (D' : W' → W' → Prop)
    (hl : ∀ s, (left s).InternalEdges D) (hr : ∀ s, (right s).InternalEdges D')
    (cl : ∀ step : Equiv.Perm W, OneOrbit step → (∀ w, D w (step w)) →
      ∃ s, (left s).FollowedBy step)
    (cr : ∀ step : Equiv.Perm W', OneOrbit step → (∀ w, D' w (step w)) →
      ∃ s, (right s).FollowedBy step)
    (hw : ∀ s i j, (left s).Wiring D i j ↔ (right s).Wiring D' i j) :
    Hamiltonian D ↔ Hamiltonian D' := by
  rw [hamiltonian_iff_wiring left D hl cl, hamiltonian_iff_wiring right D' hr cr]
  apply exists_congr
  intro s
  unfold Hamiltonian
  apply exists_congr
  intro next
  exact and_congr_right (fun _ => forall_congr' (fun i => hw s i (next i)))

end GridHardness.PathCover
