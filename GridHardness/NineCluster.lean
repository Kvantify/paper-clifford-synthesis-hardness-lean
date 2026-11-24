/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridGeometry

/-!
# Nine Cluster

[ItaiPapadimitriouSzwarcfiter1982, Lemma 2.3 and Figure 2.4].
The six witnesses below are explicit walks. Both their Hamiltonicity and use
of all four marked edges are checked by Lean's kernel with `decide`.
Numbering is row-major from the bottom left, so the paper's ports p₁,…,p₄
are 0, 2, 8, 6. Its marked edges e₁,…,e₄ are 0–3, 1–2, 5–8, 6–7.
-/

@[expose] public section

namespace GridHardness.NineCluster
open CliffordSynthesis SimpleGraph SimpleGraph.Walk

def point (i : Fin 9) : Int × Int := (i.val % 3, i.val / 3)
def graph : SimpleGraph (Fin 9) := IntegerGrid.graph (m := 8) point
instance : DecidableRel graph.Adj := gridDecidable point

def port : Fin 4 → Fin 9 := ![0, 2, 8, 6]
def markedEdges : List (Sym2 (Fin 9)) := [s(0, 3), s(1, 2), s(5, 8), s(6, 7)]

theorem point_injective : Function.Injective point := by decide

/-- Vertex order: 0, 3, 6, 7, 8, 5, 4, 1, 2. -/
def path01 : graph.Walk (port 0) (port 1) :=
  .cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 6) (.cons (by decide : graph.Adj 6 7) (.cons (by decide : graph.Adj 7 8) (.cons (by decide : graph.Adj 8 5) (.cons (by decide : graph.Adj 5 4) (.cons (by decide : graph.Adj 4 1) (.cons (by decide : graph.Adj 1 2) (.nil))))))))

/-- Vertex order: 0, 3, 6, 7, 4, 1, 2, 5, 8. -/
def path02 : graph.Walk (port 0) (port 2) :=
  .cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 6) (.cons (by decide : graph.Adj 6 7) (.cons (by decide : graph.Adj 7 4) (.cons (by decide : graph.Adj 4 1) (.cons (by decide : graph.Adj 1 2) (.cons (by decide : graph.Adj 2 5) (.cons (by decide : graph.Adj 5 8) (.nil))))))))

/-- Vertex order: 0, 3, 4, 1, 2, 5, 8, 7, 6. -/
def path03 : graph.Walk (port 0) (port 3) :=
  .cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 4) (.cons (by decide : graph.Adj 4 1) (.cons (by decide : graph.Adj 1 2) (.cons (by decide : graph.Adj 2 5) (.cons (by decide : graph.Adj 5 8) (.cons (by decide : graph.Adj 8 7) (.cons (by decide : graph.Adj 7 6) (.nil))))))))

/-- Vertex order: 2, 1, 0, 3, 6, 7, 4, 5, 8. -/
def path12 : graph.Walk (port 1) (port 2) :=
  .cons (by decide : graph.Adj 2 1) (.cons (by decide : graph.Adj 1 0) (.cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 6) (.cons (by decide : graph.Adj 6 7) (.cons (by decide : graph.Adj 7 4) (.cons (by decide : graph.Adj 4 5) (.cons (by decide : graph.Adj 5 8) (.nil))))))))

/-- Vertex order: 2, 1, 0, 3, 4, 5, 8, 7, 6. -/
def path13 : graph.Walk (port 1) (port 3) :=
  .cons (by decide : graph.Adj 2 1) (.cons (by decide : graph.Adj 1 0) (.cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 4) (.cons (by decide : graph.Adj 4 5) (.cons (by decide : graph.Adj 5 8) (.cons (by decide : graph.Adj 8 7) (.cons (by decide : graph.Adj 7 6) (.nil))))))))

/-- Vertex order: 8, 5, 2, 1, 0, 3, 4, 7, 6. -/
def path23 : graph.Walk (port 2) (port 3) :=
  .cons (by decide : graph.Adj 8 5) (.cons (by decide : graph.Adj 5 2) (.cons (by decide : graph.Adj 2 1) (.cons (by decide : graph.Adj 1 0) (.cons (by decide : graph.Adj 0 3) (.cons (by decide : graph.Adj 3 4) (.cons (by decide : graph.Adj 4 7) (.cons (by decide : graph.Adj 7 6) (.nil))))))))

/-- Lemma 2.3, including the four reserved edges needed when attaching
return tentacles. No external search result is trusted. -/
theorem nine_cluster_route (i j : Fin 4) (hij : i < j) :
    ∃ p : graph.Walk (port i) (port j), p.IsHamiltonian ∧
      ∀ e ∈ markedEdges, e ∈ p.edges := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact ⟨path01, by unfold Walk.IsHamiltonian; decide, by decide⟩
  · exact ⟨path02, by unfold Walk.IsHamiltonian; decide, by decide⟩
  · exact ⟨path03, by unfold Walk.IsHamiltonian; decide, by decide⟩
  · exact ⟨path12, by unfold Walk.IsHamiltonian; decide, by decide⟩
  · exact ⟨path13, by unfold Walk.IsHamiltonian; decide, by decide⟩
  · exact ⟨path23, by unfold Walk.IsHamiltonian; decide, by decide⟩

end GridHardness.NineCluster
