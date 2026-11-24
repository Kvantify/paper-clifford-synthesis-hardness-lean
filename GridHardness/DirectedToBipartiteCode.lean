/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedToBipartite
public import CliffordComplexity.Graphs
public import CliffordComplexity.Numbering

/-!
# Directed To Bipartite Code

Generate the internal path edges and external arc edges of the bipartite graph
using the vertex numbering of the directed graph.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.DirectedToBipartite
open CliffordComplexity

/-- Four positions per source vertex; the labels themselves are immaterial. -/
def verticesCode : Code GraphTy (.list .nat) :=
  Code.append (Code.append gVertices gVertices) (Code.append gVertices gVertices)

def blockBase : Code .nat .nat := Code.mul .id (.const .nat 4)

def internalAt : Code .nat (.list (.pair .nat .nat)) :=
  Code.append
    (.comp (.pair blockBase (Code.add blockBase (.const .nat 1))) .listSingle)
    (Code.append
      (.comp (.pair (Code.add blockBase (.const .nat 1))
        (Code.add blockBase (.const .nat 2))) .listSingle)
      (.comp (.pair (Code.add blockBase (.const .nat 2))
        (Code.add blockBase (.const .nat 3))) .listSingle))

def internalCode : Code GraphTy (.list (.pair .nat .nat)) :=
  .comp positions (.comp (.listMap internalAt) .listJoin)

def externalAt : Code (.pair .nat .nat) (.pair .nat .nat) :=
  .pair (Code.add (.comp .fst blockBase) (.const .nat 3)) (.comp .snd blockBase)

def externalCode : Code GraphTy (.list (.pair .nat .nat)) :=
  .comp gEdges (.listMap externalAt)

/-- The actual list program: three internal edges per vertex and one edge
per input arc. Out-of-range input arcs remain out of range after scaling. -/
def code : Code GraphTy GraphTy :=
  .pair verticesCode (.pair (Code.append internalCode externalCode) (.const .nat 0))

theorem verticesCode_length (x : GraphTy.denote) :
    (verticesCode.eval x).length = x.1.length * 4 := by
  change ((x.1 ++ x.1) ++ (x.1 ++ x.1)).length = _
  simp only [List.length_append]
  omega

theorem internalAt_eval (i : Nat) : internalAt.eval i =
    [(i * 4, i * 4 + 1), (i * 4 + 1, i * 4 + 2), (i * 4 + 2, i * 4 + 3)] := rfl

theorem internalCode_eval (x : GraphTy.denote) : internalCode.eval x =
    ((List.range x.1.length).map fun i =>
      [(i * 4, i * 4 + 1), (i * 4 + 1, i * 4 + 2), (i * 4 + 2, i * 4 + 3)]).flatten := by
  change ((positions.eval x).map internalAt.eval).flatten = _
  rw [positions_eval]
  rfl

theorem externalCode_eval (x : GraphTy.denote) : externalCode.eval x =
    x.2.1.map (fun p => (p.1 * 4 + 3, p.2 * 4)) := rfl

def numbering (n : Nat) : Numbering (Fin n × Fin 4) :=
  (Numbering.fin n).prod (Numbering.fin 4)

@[simp] theorem numbering_val {n : Nat} (u : Fin n × Fin 4) :
    (numbering n).num u = u.1.val * 4 + u.2.val := rfl

noncomputable def equivDecode (x : GraphTy.denote) :
    (Fin x.1.length × Fin 4) ≃ (decodeGraph (code.eval x)).V :=
  (numbering x.1.length).equivFin.trans (finCongr (verticesCode_length x).symm)

@[simp] theorem equivDecode_val (x : GraphTy.denote) (u : Fin x.1.length × Fin 4) :
    (equivDecode x u).val = u.1.val * 4 + u.2.val := rfl

theorem internalCode_mem (x : GraphTy.denote) (u v : Fin x.1.length × Fin 4) :
    ((numbering _).num u, (numbering _).num v) ∈ internalCode.eval x ↔
      u.1 = v.1 ∧ u.2.val + 1 = v.2.val := by
  rw [internalCode_eval, List.mem_flatten]
  simp only [List.mem_map, List.mem_range, numbering_val]
  constructor
  · rintro ⟨l, ⟨i, hi, rfl⟩, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
    have hu := u.2.isLt
    have hv := v.2.isLt
    have hvv : u.1.val = v.1.val := by rcases he with he | he | he <;> omega
    exact ⟨Fin.ext hvv, by rcases he with he | he | he <;> omega⟩
  · rintro ⟨heq, hs⟩
    refine ⟨_, ⟨u.1.val, u.1.isLt, rfl⟩, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    have hv := v.2.isLt
    have he := congrArg Fin.val heq
    omega

theorem externalCode_mem (x : GraphTy.denote) (u v : Fin x.1.length × Fin 4) :
    ((numbering _).num u, (numbering _).num v) ∈ externalCode.eval x ↔
      u.2 = 3 ∧ v.2 = 0 ∧ (u.1.val, v.1.val) ∈ x.2.1 := by
  rw [externalCode_eval, List.mem_map]
  simp only [Prod.mk.injEq, numbering_val]
  constructor
  · rintro ⟨⟨a,b⟩, hab, he⟩
    change Nat at a b
    change a * 4 + 3 = u.1.val * 4 + u.2.val ∧ b * 4 = v.1.val * 4 + v.2.val at he
    have hu := u.2.isLt
    have hv := v.2.isLt
    have ha : a = u.1.val := by omega
    have hb : b = v.1.val := by omega
    refine ⟨Fin.ext ?_, Fin.ext ?_, ?_⟩
    · change u.2.val = 3; omega
    · change v.2.val = 0; omega
    · simpa [ha, hb] using hab
  · rintro ⟨hu, hv, hab⟩
    exact ⟨(u.1.val, v.1.val), hab, by simp [hu, hv]⟩

theorem equivDecode_adj (x : GraphTy.denote) (u v : Fin x.1.length × Fin 4) :
    (graph (fun a b : Fin x.1.length => (a.val, b.val) ∈ x.2.1)).Adj u v ↔
      (decodeGraph (code.eval x)).G.Adj (equivDecode x u) (equivDecode x v) := by
  rw [decodeGraph_adj]
  have hmem (a b : Fin x.1.length × Fin 4) :
      ((equivDecode x a).val, (equivDecode x b).val) ∈ (code.eval x).2.1 ↔
        (a.1 = b.1 ∧ a.2.val + 1 = b.2.val) ∨
        (a.2 = 3 ∧ b.2 = 0 ∧ (a.1.val, b.1.val) ∈ x.2.1) := by
    change ((numbering _).num a, (numbering _).num b) ∈
      internalCode.eval x ++ externalCode.eval x ↔ _
    rw [List.mem_append, internalCode_mem, externalCode_mem]
  rw [hmem, hmem]
  constructor
  · intro h
    refine ⟨fun he => (graph _).ne_of_adj h ((equivDecode x).injective he), ?_⟩
    rcases h with ⟨he, hs | hs⟩ | he | he
    · exact Or.inl (Or.inl ⟨he, hs⟩)
    · exact Or.inr (Or.inl ⟨he.symm, hs⟩)
    · exact Or.inl (Or.inr he)
    · exact Or.inr (Or.inr ⟨he.2.1, he.1, he.2.2⟩)
  · rintro ⟨_, (⟨he, hs⟩ | he) | (⟨he, hs⟩ | he)⟩
    · exact Or.inl ⟨he, Or.inl hs⟩
    · exact Or.inr (Or.inl he)
    · exact Or.inl ⟨he.symm, Or.inr hs⟩
    · exact Or.inr (Or.inr ⟨he.2.1, he.1, he.2.2⟩)

noncomputable def decodeIso (x : GraphTy.denote) :
    graph (fun a b : Fin x.1.length => (a.val, b.val) ∈ x.2.1) ≃g
      (decodeGraph (code.eval x)).G where
  toEquiv := equivDecode x
  map_rel_iff' := fun {a b} => (equivDecode_adj x a b).symm

/-- The encoded output itself, including on malformed inputs, is bipartite. -/
theorem code_colorable_two (x : GraphTy.denote) :
    (decodeGraph (code.eval x)).G.Colorable 2 := by
  exact ⟨(coloring (fun a b : Fin x.1.length => (a.val, b.val) ∈ x.2.1)).comp
    (decodeIso x).symm.toHom⟩

theorem code_degree_le_three (x : GraphTy.denote)
    (hin : ∀ v : Fin x.1.length,
      (Finset.univ.filter (fun w : Fin x.1.length => (w.val, v.val) ∈ x.2.1)).card ≤ 2)
    (hout : ∀ v : Fin x.1.length,
      (Finset.univ.filter (fun w : Fin x.1.length => (v.val, w.val) ∈ x.2.1)).card ≤ 2)
    (v : (decodeGraph (code.eval x)).V) : (decodeGraph (code.eval x)).G.degree v ≤ 3 := by
  obtain ⟨w, rfl⟩ := (decodeIso x).surjective v
  letI : DecidableRel (fun a b : Fin x.1.length => (a.val, b.val) ∈ x.2.1) :=
    fun a b => inferInstanceAs (Decidable ((a.val, b.val) ∈ x.2.1))
  rw [(decodeIso x).degree_eq]
  exact degree_le_three _ hin hout w

/-- Directed Hamiltonicity on the explicit vertex/arc encoding. A nonempty
vertex set is required; a singleton with a self-loop is a directed cycle. -/
def DIRECTED_HAMILTONIAN_CYCLE : Problem GraphTy.denote := fun x =>
  0 < x.1.length ∧ ∃ next : Fin x.1.length ≃ Fin x.1.length,
    OneOrbit next ∧ ∀ v, (v.val, (next v).val) ∈ x.2.1

theorem code_correct (x : GraphTy.denote) :
    DIRECTED_HAMILTONIAN_CYCLE x ↔ Concrete.HAMILTONIAN_CIRCUIT (code.eval x) := by
  have hrename := exists_isHamiltonianCycle_iff_of_equiv
    (equivDecode x) (equivDecode_adj x)
  change DIRECTED_HAMILTONIAN_CYCLE x ↔
    ∃ (a : (decodeGraph (code.eval x)).V)
      (p : (decodeGraph (code.eval x)).G.Walk a a), p.IsHamiltonianCycle
  rw [← hrename]
  by_cases hn : 0 < x.1.length
  · have : Nonempty (Fin x.1.length) := ⟨⟨0, hn⟩⟩
    rw [hamiltonianCycle_iff]
    exact and_iff_right hn
  · constructor
    · intro h
      exact False.elim (hn h.1)
    · rintro ⟨⟨a, _⟩, _, _⟩
      exact False.elim (hn (Nat.zero_lt_of_lt a.isLt))

/-- Fully certified program for the directed-to-bipartite cycle reduction. -/
def certified : CertifiedReduction DIRECTED_HAMILTONIAN_CYCLE Concrete.HAMILTONIAN_CIRCUIT :=
  ⟨code, code_correct⟩

def BIPARTITE_HAMILTONIAN_CYCLE : Problem GraphTy.denote := fun x =>
  Concrete.HAMILTONIAN_CIRCUIT x ∧ (decodeGraph x).G.Colorable 2

/-- The same program is a reduction to the explicitly restricted bipartite
source, rather than relying on a promise about its output. -/
def certifiedBipartite :
    CertifiedReduction DIRECTED_HAMILTONIAN_CYCLE BIPARTITE_HAMILTONIAN_CYCLE where
  code := code
  correct x := ⟨fun h => ⟨(code_correct x).mp h, code_colorable_two x⟩,
    fun h => (code_correct x).mpr h.1⟩

/-- Empty, loop, and out-of-range cases use the same total program. -/
example : ¬ DIRECTED_HAMILTONIAN_CYCLE ([], ([(0, 0)], 0)) := by
  intro h
  exact Nat.not_lt_zero _ h.1

example : DIRECTED_HAMILTONIAN_CYCLE ([0], ([(0, 0)], 0)) := by
  refine ⟨by decide, Equiv.refl _, ?_, ?_⟩
  · intro u v
    change Fin 1 at u v
    exact ⟨0, Subsingleton.elim (α := Fin 1) u v⟩
  · intro v
    fin_cases v
    decide

example : code.eval ([0], ([(0, 0), (1, 0)], 0)) =
    ([0, 0, 0, 0], ([(0, 1), (1, 2), (2, 3), (3, 0), (7, 0)], 0)) := rfl

end GridHardness.DirectedToBipartite
