/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatClause
public import GridHardness.XorGadget
public import Mathlib.Data.List.Zip
public import Mathlib.Data.Fintype.Sum

/-!
# Planar SAT Assembly

The concrete variable/clause/XOR assembly from Bosboom et al. (2020),
Figure 6. This is the graph before expanding crossing XOR lines. Vertices
are explicitly tagged, so different occurrences of the same variable are
never identified. The construction contains three sentinel vertices to
handle empty formulae without an empty or singleton Hamiltonian cycle.

This file defines an actual directed graph, not a SAT-dependent target
predicate. The correctness and planarization theorems must be supplied
separately before it is a reduction to the planar source.
-/

@[expose] public section

namespace GridHardness.PlanarSatAssembly

abbrev Formula (n m : Nat) := Fin m → Fin 3 → Fin n
abbrev Occurrence (m : Nat) := Fin m × Fin 3
abbrev Vertex (n m : Nat) :=
  Fin 3 ⊕ ((Fin n × Bool) ⊕ ((Fin m × Fin 12) ⊕ (Occurrence m × Fin 8)))

set_option synthInstance.maxSize 256 in
instance (n m : Nat) : DecidableEq (Vertex n m) := by
  unfold Vertex Occurrence
  infer_instance

instance (n m : Nat) : BEq (Vertex n m) := instBEqOfDecidableEq
instance (n m : Nat) : LawfulBEq (Vertex n m) := by
  infer_instance

def sent {n m : Nat} (i : Fin 3) : Vertex n m := Sum.inl i
def var {n m : Nat} (i : Fin n) (exit : Bool) : Vertex n m := Sum.inr (Sum.inl (i, exit))
def clause {n m : Nat} (i : Fin m) (j : Fin 12) : Vertex n m :=
  Sum.inr (Sum.inr (Sum.inl (i, j)))
def xor {n m : Nat} (o : Occurrence m) (j : Fin 8) : Vertex n m :=
  Sum.inr (Sum.inr (Sum.inr (o, j)))

def occurrences (m : Nat) : List (Occurrence m) :=
  (List.finRange m).flatMap (fun c => (List.finRange 3).map (c, ·))

def occurrencesOf {n m : Nat} (φ : Formula n m) (v : Fin n) : List (Occurrence m) :=
  (occurrences m).filter (fun o => decide (φ o.1 o.2 = v))

def clauseBottom : Fin 3 → Fin 12 := ![0, 4, 8]
def clauseTop : Fin 3 → Fin 12 := ![1, 5, 9]

/-- Endpoints of each block on the outer directed backbone. -/
def slots (n m : Nat) : List (Vertex n m × Vertex n m) :=
  [(sent 0, sent 2)] ++
  (List.finRange n).map (fun v => (var v false, var v true)) ++
  (List.finRange m).map (fun c => (clause c 8, clause c 1))

def backbone (n m : Nat) : List (Vertex n m × Vertex n m) :=
  ((slots n m).map Prod.snd).zip (((slots n m).map Prod.fst).tail ++ [sent 0])

/-- A variable's true branch passes consecutively through the left ports
of every occurrence XOR. Its false branch is the direct edge. The links
introduce no extra vertices, which would otherwise be unvisited when false. -/
def variableChain {n m : Nat} (φ : Formula n m) (v : Fin n) :
    List (Vertex n m × Vertex n m) :=
  (var v false :: (occurrencesOf φ v).map (fun o => xor o 0)).zip
    ((occurrencesOf φ v).map (fun o => xor o 3) ++ [var v true])

/-- The fourteen clause edges left after removing its three right edges.
Those three edges are replaced by the right ports of occurrence XORs. -/
def clauseBody : List (Fin 12 × Fin 12) :=
  [(0, 3), (2, 1), (2, 3), (3, 6),
   (4, 7), (5, 0), (6, 5), (6, 7), (7, 10),
   (8, 11), (9, 4), (10, 9), (10, 11), (11, 2)]

def clauseEdges {n m : Nat} (c : Fin m) : List (Vertex n m × Vertex n m) :=
  clauseBody.map (fun (u, v) => (clause c u, clause c v))

def clauseLinks {n m : Nat} (o : Occurrence m) : List (Vertex n m × Vertex n m) :=
  [(clause o.1 (clauseBottom o.2), xor o 4),
   (xor o 7, clause o.1 (clauseTop o.2))]

def xorEdges {n m : Nat} (o : Occurrence m) : List (Vertex n m × Vertex n m) :=
  (List.finRange 10).map (fun e => (xor o (XorGadget.arc e).1, xor o (XorGadget.arc e).2))

/-- A finite edge-list constructor independent of any truth assignment. -/
def edges {n m : Nat} (φ : Formula n m) : List (Vertex n m × Vertex n m) :=
  [(sent 0, sent 1), (sent 1, sent 2)] ++ backbone n m ++
  (List.finRange n).flatMap (fun v => (var v false, var v true) :: variableChain φ v) ++
  (List.finRange m).flatMap clauseEdges ++
  (occurrences m).flatMap (fun o => clauseLinks o ++ xorEdges o)

def Adj {n m : Nat} (φ : Formula n m) (u v : Vertex n m) : Prop := (u, v) ∈ edges φ

set_option synthInstance.maxSize 1024 in
instance {n m : Nat} (φ : Formula n m) : DecidableRel (Adj φ) := by
  letI : BEq (Vertex n m × Vertex n m) := instBEqOfDecidableEq
  exact fun u v => inferInstanceAs (Decidable ((u, v) ∈ edges φ))

def Satisfies {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool) : Prop :=
  ∀ c, ((List.finRange 3).filter (fun j => σ (φ c j))).length = 1

def Satisfiable {n m : Nat} (φ : Formula n m) : Prop := ∃ σ, Satisfies φ σ

theorem vertex_card (n m : Nat) : Fintype.card (Vertex n m) = 3 + 2 * n + 36 * m := by
  simp [Vertex, Occurrence, Fintype.card_sum, Fintype.card_prod]
  omega

theorem vertex_card_ge_three (n m : Nat) : 3 ≤ Fintype.card (Vertex n m) := by
  rw [vertex_card]
  omega

@[simp] theorem occurrences_length (m : Nat) : (occurrences m).length = 3 * m := by
  simp [occurrences, List.length_flatMap, List.sum_replicate, Nat.mul_comm]

theorem occurrencesOf_length_le {n m : Nat} (φ : Formula n m) (v : Fin n) :
    (occurrencesOf φ v).length ≤ 3 * m := by
  exact (List.length_filter_le _ _).trans_eq (occurrences_length m)

@[simp] theorem variableChain_length {n m : Nat} (φ : Formula n m) (v : Fin n) :
    (variableChain φ v).length = (occurrencesOf φ v).length + 1 := by
  simp [variableChain, Nat.add_comm]

@[simp] theorem slots_length (n m : Nat) : (slots n m).length = n + m + 1 := by
  simp [slots]

@[simp] theorem backbone_length (n m : Nat) : (backbone n m).length = n + m + 1 := by
  simp [backbone]

@[simp] theorem clauseEdges_length {n m : Nat} (c : Fin m) :
    (clauseEdges (n := n) c).length = 14 := by
  simp [clauseEdges, clauseBody]

@[simp] theorem clauseLinks_length {n m : Nat} (o : Occurrence m) :
    (clauseLinks (n := n) o).length = 2 := by rfl

@[simp] theorem xorEdges_length {n m : Nat} (o : Occurrence m) :
    (xorEdges (n := n) o).length = 10 := by simp [xorEdges]

/-- A polynomial bound on the explicitly produced edge-list size. This
combinatorial bound does not bound running time; `PlanarSatCode` certifies construction cost. -/
theorem edges_length_le {n m : Nat} (φ : Formula n m) :
    (edges φ).length ≤ 3 + 3 * n + 51 * m + 3 * n * m := by
  have hv : ((List.finRange n).flatMap
      (fun v => (var (m := m) v false, var v true) :: variableChain φ v)).length ≤
        n * (3 * m + 2) := by
    rw [List.length_flatMap]
    have hs : ∀ v ∈ List.finRange n,
        ((var (m := m) v false, var v true) :: variableChain φ v).length ≤ 3 * m + 2 := by
      intro v _
      simp only [List.length_cons, variableChain_length]
      have := occurrencesOf_length_le φ v
      omega
    calc
      _ ≤ ((List.finRange n).map (fun _ => 3 * m + 2)).sum :=
        List.sum_le_sum (by simpa using hs)
      _ = n * (3 * m + 2) := by simp
  simp only [edges, List.length_append, List.length_cons, List.length_nil,
    backbone_length, List.length_flatMap, clauseEdges_length,
    clauseLinks_length, xorEdges_length] at *
  simp only [List.map_const', List.length_finRange, List.sum_replicate,
    occurrences_length, nsmul_eq_mul] at *
  nlinarith

theorem backbone_no_xor_source {n m : Nat} (o : Occurrence m) (i : Fin 8)
    (v : Vertex n m) : (xor o i, v) ∉ backbone n m := by
  intro h
  have hm := (List.of_mem_zip h).1
  simp [slots, xor, sent, var, clause] at hm

theorem backbone_no_xor_target {n m : Nat} (o : Occurrence m) (i : Fin 8)
    (v : Vertex n m) : (v, xor o i) ∉ backbone n m := by
  intro h
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | hm
  · have := List.mem_of_mem_tail hm
    simp [slots, xor, sent, var, clause] at this
  · simp [xor, sent] at hm

/-- Only the XOR's left exit can source a variable-chain link. -/
theorem variableChain_xor_source {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) (i : Fin 8) (w : Vertex n m)
    (h : (xor o i, w) ∈ variableChain φ v) : i = 0 := by
  have hm := (List.of_mem_zip h).1
  simp [xor, var] at hm
  aesop

/-- Only the XOR's left entry can receive a variable-chain link. -/
theorem variableChain_xor_target {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) (i : Fin 8) (w : Vertex n m)
    (h : (w, xor o i) ∈ variableChain φ v) : i = 3 := by
  have hm := (List.of_mem_zip h).2
  simp [xor, var] at hm
  aesop

theorem xor_injective {n m : Nat} (o : Occurrence m) :
    Function.Injective (xor (n := n) o) := by
  intro u v h
  simpa [xor] using h

/-- Apart from its two exit ports, each XOR vertex has only the gadget's
listed outgoing edges, even after all variables and clauses are assembled. -/
theorem xor_outgoing {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (i : Fin 8) (hi0 : i ≠ 0) (hi7 : i ≠ 7) (w : Vertex n m)
    (h : Adj φ (xor o i) w) :
    ∃ e : Fin 10, (XorGadget.arc e).1 = i ∧ w = xor o (XorGadget.arc e).2 := by
  simp only [Adj, edges, List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor, sent] at hs
  · exact False.elim (backbone_no_xor_source o i w hb)
  · obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor, var] at hv
    · exact False.elim (hi0 (variableChain_xor_source φ v o i w hv))
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges, xor, clause] at hc
  · obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at ha
      rcases ha with ⟨ha, _⟩ | ⟨ha, _⟩
      · simp [clause, xor] at ha
      · have : i = 7 := by
          simpa [xor] using (congrArg Prod.snd
            (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj ha))))
        exact False.elim (hi7 this)
    · obtain ⟨e, _, he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor, Sum.inr.injEq, Prod.mk.injEq] at hsrc
      rcases hsrc with ⟨rfl, hsrc⟩
      exact ⟨e, hsrc, hdst.symm⟩

/-- Apart from its two entry ports, an XOR has no incoming edge from any
other gadget. This is the reverse isolation property needed for extraction. -/
theorem xor_incoming {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (i : Fin 8) (hi3 : i ≠ 3) (hi4 : i ≠ 4) (w : Vertex n m)
    (h : Adj φ w (xor o i)) :
    ∃ e : Fin 10, (XorGadget.arc e).2 = i ∧ w = xor o (XorGadget.arc e).1 := by
  simp only [Adj, edges, List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor, sent] at hs
  · exact False.elim (backbone_no_xor_target o i w hb)
  · obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor, var] at hv
    · exact False.elim (hi3 (variableChain_xor_target φ v o i w hv))
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges, xor, clause] at hc
  · obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at ha
      rcases ha with ⟨_, ha⟩ | ⟨_, ha⟩
      · have : i = 4 := by
          simpa [xor] using (congrArg Prod.snd
            (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj ha))))
        exact False.elim (hi4 this)
      · simp [clause, xor] at ha
    · obtain ⟨e, _, he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor, Sum.inr.injEq, Prod.mk.injEq] at hdst
      rcases hdst with ⟨rfl, hdst⟩
      exact ⟨e, hdst, hsrc.symm⟩

end GridHardness.PlanarSatAssembly
