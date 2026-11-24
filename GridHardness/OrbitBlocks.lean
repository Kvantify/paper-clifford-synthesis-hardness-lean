/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrbitSplicing
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# Orbit Blocks

A four-block decomposition of the single orbit of a finite successor map.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness

/-- Subdividing every successor step into four steps preserves a spanning
orbit. Stating this in terms of the four equations permits direct reuse for
different concrete graph encodings. -/
theorem OneOrbit.four_blocks {V : Type*} {next : V → V}
    (h : OneOrbit next) (step : V × Fin 4 → V × Fin 4)
    (h0 : ∀ v, step (v, 0) = (v, 1))
    (h1 : ∀ v, step (v, 1) = (v, 2))
    (h2 : ∀ v, step (v, 2) = (v, 3))
    (h3 : ∀ v, step (v, 3) = (next v, 0)) : OneOrbit step := by
  apply h.expand (fun v => (v, 0))
  · intro v
    refine ⟨4, ?_⟩
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2, h3]
  · rintro ⟨v, i⟩
    refine ⟨next v, ?_⟩
    fin_cases i
    · refine ⟨4, ?_⟩
      change step (step (step (step (v, 0)))) = _
      rw [h0, h1, h2, h3]
    · refine ⟨3, ?_⟩
      change step (step (step (v, 1))) = _
      rw [h1, h2, h3]
    · refine ⟨2, ?_⟩
      change step (step (v, 2)) = _
      rw [h2, h3]
    · exact ⟨1, h3 v⟩
  · rintro ⟨v, i⟩
    refine ⟨v, ?_⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, h0 v⟩
    · refine ⟨2, ?_⟩
      change step (step (v, 0)) = (v, 2)
      rw [h0, h1]
    · refine ⟨3, ?_⟩
      change step (step (step (v, 0))) = (v, 3)
      rw [h0, h1, h2]

end GridHardness
