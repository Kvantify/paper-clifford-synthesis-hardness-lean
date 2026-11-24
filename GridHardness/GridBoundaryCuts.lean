/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyCuts
public import GridHardness.OrbitHamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Grid Boundary Cuts

Derive the three-port cut classification from the actual graph boundary,
rather than assuming a bound on a Hamiltonian cycle's used crossings.
-/

@[expose] public section

namespace GridHardness.CycleCut
open SimpleGraph
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered boundary edges, with the endpoint inside the region first. -/
def boundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (V × V) :=
  (S.product (Finset.univ \ S)).filter (fun e => G.Adj e.1 e.2)

def usedBoundary (next : Equiv.Perm V) (S : Finset V) : Finset (V × V) :=
  (leaving next S).image (fun v => (v, next v)) ∪
    (entering next S).image (fun v => (next v, v))

theorem usedBoundary_card (next : Equiv.Perm V) (ho : OneOrbit next)
    (hcard : 3 ≤ Fintype.card V) (S : Finset V) :
    (usedBoundary next S).card = (leaving next S).card + (entering next S).card := by
  have hd : Disjoint ((leaving next S).image (fun v => (v, next v)))
      ((entering next S).image (fun v => (next v, v))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hf
    have heq := ha.trans hb.symm
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    exact ho.not_period_two hcard b (by
      change a = next b at h1
      change next a = b at h2
      rw [← h1]
      exact h2)
  rw [usedBoundary, Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]

theorem usedBoundary_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (next : Equiv.Perm V) (ha : ∀ v, G.Adj v (next v)) (S : Finset V) :
    usedBoundary next S ⊆ boundary G S := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have hv' := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hv'.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv'.2⟩⟩, ha v⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have hv' := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hv'.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv'.1⟩⟩, (ha v).symm⟩

/-- Actual geometric boundary size bounds the number of used crossings. -/
theorem crossings_le_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (next : Equiv.Perm V) (ho : OneOrbit next) (ha : ∀ v, G.Adj v (next v))
    (hcard : 3 ≤ Fintype.card V) (S : Finset V) :
    (leaving next S).card + (entering next S).card ≤ (boundary G S).card := by
  rw [← usedBoundary_card next ho hcard S]
  exact Finset.card_le_card (usedBoundary_subset G next ha S)

/-- Three available graph edges force exactly one entrance and one exit
in a nonempty proper region of an actual global spanning cycle. -/
theorem three_edge_boundary (G : SimpleGraph V) [DecidableRel G.Adj]
    (next : Equiv.Perm V) (ho : OneOrbit next) (ha : ∀ v, G.Adj v (next v))
    (hcard : 3 ≤ Fintype.card V) (S : Finset V) (hs : S.Nonempty) (hout : ∃ v, v ∉ S)
    (hb : (boundary G S).card ≤ 3) :
    (leaving next S).card = 1 ∧ (entering next S).card = 1 :=
  three_port_region next ho S hs hout ((crossings_le_boundary G next ho ha hcard S).trans hb)

private theorem pair_subset_triple {A : Type*} [DecidableEq A] (S : Finset A) (a b c : A)
    (hs : S.card = 2) (hsub : S ⊆ {a, b, c}) :
    S = {a, b} ∨ S = {a, c} ∨ S = {b, c} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  have hx := hsub (by simp : x ∈ ({x, y} : Finset A))
  have hy := hsub (by simp : y ∈ ({x, y} : Finset A))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact False.elim (hxy rfl)
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Finset.pair_comm _ _)
    | exact Or.inr (Or.inl (Finset.pair_comm _ _))
    | exact Or.inr (Or.inr (Finset.pair_comm _ _))

/-- For an actual three-edge tentacle boundary, the used edges are exactly
one of its three pairs: the two same-side ports (return) or either same-side
port together with the opposite-side port (cross). -/
theorem three_edge_pairing (G : SimpleGraph V) [DecidableRel G.Adj]
    (next : Equiv.Perm V) (ho : OneOrbit next) (ha : ∀ v, G.Adj v (next v))
    (hcard : 3 ≤ Fintype.card V) (S : Finset V) (hs : S.Nonempty) (hout : ∃ v, v ∉ S)
    (a b c : V × V) (hb : boundary G S ⊆ {a, b, c}) :
    usedBoundary next S = {a, b} ∨ usedBoundary next S = {a, c} ∨
      usedBoundary next S = {b, c} := by
  have ht : ({a, b, c} : Finset (V × V)).card ≤ 3 := by
    have h1 := Finset.card_insert_le a ({b, c} : Finset (V × V))
    have h2 := Finset.card_insert_le b ({c} : Finset (V × V))
    simp only [Finset.card_singleton] at h2
    omega
  have hle : (boundary G S).card ≤ 3 := (Finset.card_le_card hb).trans ht
  obtain ⟨hl, he⟩ := three_edge_boundary G next ho ha hcard S hs hout hle
  apply pair_subset_triple _ a b c
  · rw [usedBoundary_card next ho hcard S, hl, he]
  · exact (usedBoundary_subset G next ha S).trans hb

end GridHardness.CycleCut
