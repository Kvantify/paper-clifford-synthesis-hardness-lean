/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.Hamiltonian

/-!
# Cycle To Path

The forced-edge step in [ItaiPapadimitriouSzwarcfiter1982, Corollary 1].
We use actual Hamiltonian cycles, excluding mathlib's singleton convention.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness
open SimpleGraph SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V}

/-- At a vertex of degree two, either incident edge can be opened to turn a
Hamiltonian cycle into a Hamiltonian path with the prescribed endpoints.
The size hypothesis excludes the two-vertex path, which is not a cycle. -/
theorem cycle_iff_path_of_degree_two (hcard : 3 ≤ Fintype.card V)
    (hdegree : G.degree s = 2) (hadj : G.Adj s t) :
    (∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle) ↔
      ∃ p : G.Walk s t, p.IsHamiltonian := by
  constructor
  · rintro ⟨a, p, hp⟩
    let r := p.rotate s (hp.mem_support s)
    have hr : r.IsHamiltonianCycle := hp.rotate _
    have he : r.toSubgraph.Adj s t :=
      (adj_toSubgraph_iff_of_degree_eq_two hr hdegree t).mpr hadj
    obtain ⟨q, hq, hsnd, hverts⟩ := hr.isCycle.exists_isCycle_snd_verts_eq he
    have hmem : ∀ v, v ∈ q.support := by
      intro v
      rw [← q.mem_verts_toSubgraph, hverts, r.mem_verts_toSubgraph]
      exact hr.mem_support v
    have ht : q.tail.IsHamiltonian := by
      apply hq.isPath_tail.isHamiltonian_of_mem
      intro v
      by_cases h : v = s
      · subst v
        exact q.tail.end_mem_support
      · rw [support_tail_of_not_nil q hq.not_nil]
        have hm := hmem v
        rw [← cons_tail_support q, List.mem_cons] at hm
        exact hm.resolve_left h
    refine ⟨q.tail.reverse.copy rfl hsnd, ?_⟩
    intro v
    simpa only [support_copy, support_reverse, List.count_reverse] using ht v
  · rintro ⟨p, hp⟩
    refine ⟨t, .cons hadj.symm p, ?_, ?_⟩
    · apply isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simpa using hp.isPath
      · have := hp.length_eq
        simp only [length_cons]
        omega
    · intro v
      simpa only [tail_cons, support_copy] using hp v

end GridHardness
