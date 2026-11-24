/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PositiveSat
public import GridHardness.PlanarSatAssembly
public import Mathlib.Data.Set.Function
import Mathlib.Data.List.GetD

/-!
# Positive SAT Finite

Reindex the variables in a positive formula by a finite type, preserving satisfiability.
-/

@[expose] public section

namespace GridHardness
open CliffordComplexity Cslib.Logic.PL

/-- Renumber positive SAT variable occurrences by their positions in the variable list. -/
def finiteFormula (x : SatTy.denote) :
    PlanarSatAssembly.Formula ((vsOf x).length + 1) x.length :=
  fun c j => varSlot (vsOf x) (((x.get c).getD j.val (0, true)).1)

private def formulaCNF {n m : Nat} (φ : PlanarSatAssembly.Formula n m) : CNF (Fin n) :=
  List.ofFn fun c => List.ofFn fun j => (φ c j, true)

private theorem formulaCNF_oneSat {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (σ : Fin n → Bool) :
    (formulaCNF φ).evalOne σ = true ↔ PlanarSatAssembly.Satisfies φ σ := by
  have beqTrue (b : Bool) : (b == true) = b := by cases b <;> rfl
  simp only [CNF.evalOne_eq_true_iff, formulaCNF, List.ofFn_eq_map, List.forall_mem_map,
    List.mem_finRange, true_implies, Clause.evalOne_eq_true_iff, List.countP_map,
    Function.comp_def, Literal.eval, beqTrue, PlanarSatAssembly.Satisfies]
  simp only [List.countP_eq_length_filter]

private theorem finiteFormula_cnf (x : SatTy.denote)
    (hw : ∀ c ∈ x, c.length = 3) (hp : ∀ c ∈ x, ∀ p ∈ c, p.2 = true) :
    formulaCNF (finiteFormula x) = CNF.relabel (varSlot (vsOf x)) x := by
  apply List.ext_getElem (by simp [formulaCNF, CNF.relabel])
  intro i hi hj
  simp only [formulaCNF, List.getElem_ofFn, CNF.relabel, List.getElem_map]
  have hix : i < x.length := by simpa [formulaCNF] using hi
  have hwidth := hw x[i] (List.getElem_mem hix)
  apply List.ext_getElem (by simp [Clause.relabel, hwidth])
  intro j hja hjb
  have hj3 : j < 3 := by simpa only [List.length_ofFn] using hja
  have hjc : j < x[i].length := by omega
  simp only [Clause.relabel, List.getElem_ofFn, List.getElem_map]
  change (varSlot (vsOf x) ((x[i].getD j (0, true)).1), true) =
    (varSlot (vsOf x) (x[i][j].1), x[i][j].2)
  rw [List.getD_eq_getElem _ _ hjc, hp _ (List.getElem_mem hix) _ (List.getElem_mem hjc)]

theorem finiteFormula_correct (x : SatTy.denote)
    (hw : ∀ c ∈ x, c.length = 3) (hp : ∀ c ∈ x, ∀ p ∈ c, p.2 = true) :
    PlanarSatAssembly.Satisfiable (finiteFormula x) ↔
      Concrete.MONOTONE_ONE_IN_THREE_SAT3 x := by
  change (∃ σ, PlanarSatAssembly.Satisfies (finiteFormula x) σ) ↔ _
  simp only [← formulaCNF_oneSat, finiteFormula_cnf x hw hp, CNF.evalOne_relabel]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨hp, hw, σ ∘ varSlot (vsOf x), hσ⟩
  · rintro ⟨_, _, σ, hσ⟩
    let f := varSlot (vsOf x)
    have inj : Set.InjOn f {v | v ∈ CNF.vars (V := Nat) x} := fun _ hu _ hv h =>
      varSlot_inj ((mem_vsOf x).mpr hu) ((mem_vsOf x).mpr hv) h
    let τ := σ ∘ Function.invFunOn f {v | v ∈ CNF.vars (V := Nat) x}
    refine ⟨τ, ?_⟩
    rw [CNF.evalOne_congr (σ := τ ∘ f) (τ := σ) (fun v hv => ?_)]
    · exact hσ
    · change σ (Function.invFunOn f _ (f v)) = σ v
      rw [inj.leftInvOn_invFunOn hv]

end GridHardness
