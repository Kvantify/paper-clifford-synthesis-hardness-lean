/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.ListPrograms
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Graphs

Polynomial-time encodings of numbered finite graphs, with programs for extracting vertex
indices and edge lists.
-/

@[expose] public section

namespace CliffordComplexity

/-- Numbered vertices, an ordered list of endpoint pairs, and a natural parameter. -/
abbrev GraphTy := Ty.pair (.list .nat) (.pair (.list (.pair .nat .nat)) .nat)

/-- Read the list of vertex labels from the encoded graph. -/
def gVertices : Code GraphTy (.list .nat) := .fst

/-- Read the list of endpoint pairs from the encoded graph. -/
def gEdges : Code GraphTy (.list (.pair .nat .nat)) := .comp .snd .fst

/-- Enumerate the vertex positions regardless of the stored labels. -/
def positions : Code GraphTy (.list .nat) := .comp gVertices Code.indices

theorem positions_eval (x : GraphTy.denote) : positions.eval x = List.range x.1.length :=
  indices_eval (t := .nat) x.1

/-- A simple graph bundled with its vertex type. -/
structure IndexedGraph where
  /-- The finite interval of vertex positions after decoding. -/
  V : Type
  /-- The undirected graph on those positions. -/
  G : SimpleGraph V

/-- Treat the recorded edges as undirected and omit self-loops. -/
@[reducible] def decodeGraph (x : GraphTy.denote) : IndexedGraph where
  V := Fin x.1.length
  G := SimpleGraph.fromRel fun i j => (i.val, j.val) ∈ x.2.1

theorem decodeGraph_adj (x : GraphTy.denote) (u v : (decodeGraph x).V) :
    (decodeGraph x).G.Adj u v ↔
      u ≠ v ∧ ((u.val, v.val) ∈ x.2.1 ∨ (v.val, u.val) ∈ x.2.1) :=
  SimpleGraph.fromRel_adj _ _ _

instance (x : GraphTy.denote) : DecidableRel (decodeGraph x).G.Adj :=
  fun u v => decidable_of_iff _ (decodeGraph_adj x u v).symm

namespace Concrete

/-- The language of encoded graphs admitting a Hamiltonian cycle. -/
def HAMILTONIAN_CIRCUIT (x : GraphTy.denote) : Prop :=
  ∃ a : (decodeGraph x).V, ∃ p : (decodeGraph x).G.Walk a a, p.IsHamiltonianCycle

end Concrete
end CliffordComplexity
