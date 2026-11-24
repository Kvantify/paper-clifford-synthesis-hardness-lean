/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridPointCode

/-!
# Grid Assembly Code

Certified reductions from explicitly padded rectangle unions to the
encoded grid problems, and their semantic connection to valid global cluster
assemblies. No loop is controlled by a binary coordinate or side length.
-/

@[expose] public section

namespace GridHardness.GridPointCode
open CliffordSynthesis SimpleGraph OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Any duplicate-free coordinate list representing a finite set denotes its
actual induced grid, regardless of the enumeration order. -/
theorem encoded_cycle_iff (L : CycleInputTy.denote) (S : Finset Point)
    (hn : (L.map decoded).Nodup) (hm : ∀ q, q ∈ L.map decoded ↔ q ∈ S) :
    GRID_HAMILTONIAN_CYCLE L ↔
      ∃ (v : S) (p : (finiteGrid S).Walk v v), p.IsHamiltonianCycle := by
  cases L with
  | nil =>
    apply iff_of_false empty_not_grid_cycle
    rintro ⟨v, _, _⟩
    have h := (hm v.val).mpr v.property
    simp only [List.map_nil, List.not_mem_nil] at h
  | cons a L =>
    have hi : Function.Injective (decoded ∘ (a :: L).get) := by
      intro i j he
      apply Fin.ext
      have hi : i.val < ((a :: L).map decoded).length := by simpa using i.isLt
      have hj : j.val < ((a :: L).map decoded).length := by simpa using j.isLt
      apply (hn.getElem_inj_iff (hi := hi) (hj := hj)).mp
      simpa only [List.getElem_map, List.get_eq_getElem, Function.comp_apply] using he
    let f : Fin (L.length + 1) → S := fun i =>
      ⟨decoded ((a :: L).get i), (hm _).mp (List.mem_map_of_mem (List.get_mem _ _))⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j he
        exact hi (congrArg Subtype.val he)
      · intro v
        obtain ⟨p, hp, he⟩ := List.mem_map.mp ((hm v.val).mpr v.property)
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
        exact ⟨i, Subtype.ext he⟩
    let e : Fin (L.length + 1) ≃ S := Equiv.ofBijective f hf
    have hL : a :: L = List.ofFn (a :: L).get := (List.ofFn_get _).symm
    rw [hL, cycle_source_input]
    apply (and_iff_right hi).trans
    exact exists_isHamiltonianCycle_iff_of_equiv e (fun _ _ => Iff.rfl)

/-- The source is Hamiltonicity of the actual finite induced coordinate
union. It is not a predicate defined by running the target reduction. -/
def RECTANGLE_GRID_HAMILTONIAN_CYCLE : Problem InputTy.denote := fun rs =>
  ∃ (v : points rs) (p : (finiteGrid (points rs)).Walk v v), p.IsHamiltonianCycle

theorem code_correct (rs : InputTy.denote) :
    RECTANGLE_GRID_HAMILTONIAN_CYCLE rs ↔ GRID_HAMILTONIAN_CYCLE (code.eval rs) :=
  (encoded_cycle_iff _ _ (code_decoded_nodup rs) (code_decoded_mem rs)).symm

def certifiedToGridCycle : CertifiedReduction RECTANGLE_GRID_HAMILTONIAN_CYCLE
    GRID_HAMILTONIAN_CYCLE where
  code := code
  correct := code_correct

def certifiedToGridPath : CertifiedReduction RECTANGLE_GRID_HAMILTONIAN_CYCLE
    GRID_HAMILTONIAN_PATH := certifiedToGridCycle.comp certifiedGridCycleToPath

theorem code_length (rs : InputTy.denote) : (code.eval rs).length = (points rs).card := by
  have he : ((code.eval rs).map decoded).toFinset = points rs := by
    ext p
    exact List.mem_toFinset.trans (code_decoded_mem rs p)
  rw [← he, List.toFinset_card_of_nodup (code_decoded_nodup rs), List.length_map]

/-- Exact connection to the geometric assembly theorem. The only extra
premise identifies two explicitly computed finite coordinate sets. -/
theorem valid_layout_cycle {C : Type*} [Fintype C] [DecidableEq C]
    {l : GridAssembly.Layout C} {H : SimpleGraph C} [DecidableRel H.Adj]
    (hv : l.Valid H) (hc : 3 ≤ Fintype.card C) (hd : ∀ c, H.degree c ≤ 3)
    (rs : InputTy.denote) (hp : points rs = l.points) :
    (∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) ↔
      GRID_HAMILTONIAN_CYCLE (certifiedToGridCycle.code.eval rs) := by
  apply Iff.trans ?_ (certifiedToGridCycle.correct rs)
  change (∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) ↔
    ∃ (v : points rs) (p : (finiteGrid (points rs)).Walk v v), p.IsHamiltonianCycle
  rw [hp]
  exact (hv.hamiltonianCycle_iff hc hd).symm

theorem valid_layout_path {C : Type*} [Fintype C] [DecidableEq C]
    {l : GridAssembly.Layout C} {H : SimpleGraph C} [DecidableRel H.Adj]
    (hv : l.Valid H) (hc : 3 ≤ Fintype.card C) (hd : ∀ c, H.degree c ≤ 3)
    (rs : InputTy.denote) (hp : points rs = l.points) :
    (∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) ↔
      GRID_HAMILTONIAN_PATH (certifiedToGridPath.code.eval rs) := by
  exact (valid_layout_cycle hv hc hd rs hp).trans
    (certifiedGridCycleToPath.correct (certifiedToGridCycle.code.eval rs))

theorem valid_layout_length {C : Type*} [Fintype C]
    {l : GridAssembly.Layout C} {H : SimpleGraph C} [DecidableRel H.Adj]
    (hv : l.Valid H) (rs : InputTy.denote) (hp : points rs = l.points) :
    (code.eval rs).length = 9 * Fintype.card C + 2 * ∑ c, (l.body c).halfTentacleSize := by
  rw [code_length, hp, hv.points_card]

end GridHardness.GridPointCode
