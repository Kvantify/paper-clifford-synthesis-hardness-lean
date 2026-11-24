/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatAssembly
public import GridHardness.OrbitList
public import Mathlib.Data.List.Count

/-!
# Planar SAT Forward

Explicit forward witnesses for the SAT assembly. The expanded clause
path includes its two false-literal XORs; true-literal XORs are visited on
their variable's true branch instead.
-/

@[expose] public section

namespace GridHardness.PlanarSatForward
open PlanarSatAssembly

abbrev LocalVertex := Fin 12 ⊕ (Fin 3 × Fin 8)
instance : BEq LocalVertex := instBEqOfDecidableEq
instance : LawfulBEq LocalVertex := by infer_instance

def localEmbed {n m : Nat} (c : Fin m) : LocalVertex → Vertex n m
  | .inl v => clause c v
  | .inr (i, v) => PlanarSatAssembly.xor (c, i) v

theorem localEmbed_injective {n m : Nat} (c : Fin m) :
    Function.Injective (localEmbed (n := n) c) := by
  intro u v h
  cases u with
  | inl u => cases v <;> simp_all [localEmbed, clause, PlanarSatAssembly.xor]
  | inr u =>
      cases v <;> simp_all [localEmbed, clause, PlanarSatAssembly.xor]
      exact Prod.ext h.1 h.2

def localXorPath (i : Fin 3) : List LocalVertex :=
  XorGadget.rightVertices.map (fun v => Sum.inr (i, v))

def localNode (i : Fin 3) (v : Fin 12) : List LocalVertex :=
  [Sum.inl v] ++
    (if v = 0 ∧ i ≠ 0 then localXorPath 0 else
     if v = 4 ∧ i ≠ 1 then localXorPath 1 else
     if v = 8 ∧ i ≠ 2 then localXorPath 2 else [])

def localOrder (i : Fin 3) : List LocalVertex :=
  (List.finRange 12).flatMap (fun j => localNode i (PlanarSatClause.order i j))

def localEdges : List (LocalVertex × LocalVertex) :=
  clauseBody.map (fun (u, v) => (Sum.inl u, Sum.inl v)) ++
  (List.finRange 3).flatMap (fun i =>
    [(Sum.inl (clauseBottom i), Sum.inr (i, 4)),
      (Sum.inr (i, 7), Sum.inl (clauseTop i))] ++
    (List.finRange 10).map (fun e =>
      (Sum.inr (i, (XorGadget.arc e).1), Sum.inr (i, (XorGadget.arc e).2))))

def LocalAdj (u v : LocalVertex) : Prop := (u, v) ∈ localEdges
instance : DecidableRel LocalAdj := by
  letI : BEq (LocalVertex × LocalVertex) := instBEqOfDecidableEq
  exact fun u v => inferInstanceAs (Decidable ((u, v) ∈ localEdges))

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem localOrder_chain : ∀ i : Fin 3, (localOrder i).IsChain LocalAdj := by decide

theorem localOrder_head (i : Fin 3) : (localOrder i).head? = some (Sum.inl 8) := by
  fin_cases i <;> decide

theorem localOrder_last (i : Fin 3) : (localOrder i).getLast? = some (Sum.inl 1) := by
  fin_cases i <;> decide

theorem localOrder_length (i : Fin 3) : (localOrder i).length = 28 := by
  fin_cases i <;> decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem localOrder_count_clause : ∀ (i : Fin 3) (v : Fin 12),
    (localOrder i).count (Sum.inl v) = 1 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem localOrder_count_xor : ∀ (i j : Fin 3) (v : Fin 8),
    (localOrder i).count (Sum.inr (j, v)) = if i = j then 0 else 1 := by decide

/-- Every local edge maps to an edge of the actual assembly. -/
theorem localEmbed_adj {n m : Nat} (φ : Formula n m) (c : Fin m)
    {u v : LocalVertex} (h : LocalAdj u v) :
    Adj φ (localEmbed c u) (localEmbed c v) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨a, b⟩, hab, h⟩ := List.mem_map.mp h
    cases h
    have hc : (clause (n := n) c a, clause c b) ∈ clauseEdges c :=
      List.mem_map.mpr ⟨(a, b), hab, rfl⟩
    have hm := List.mem_flatMap.mpr ⟨c, List.mem_finRange c, hc⟩
    simp only [Adj, edges, List.mem_append]
    exact Or.inl (Or.inr hm)
  · obtain ⟨i, _, h⟩ := List.mem_flatMap.mp h
    have hm : (localEmbed (n := n) c u, localEmbed c v) ∈
        clauseLinks (c, i) ++ xorEdges (c, i) := by
      rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> cases h <;>
          simp [localEmbed, clauseLinks]
      · obtain ⟨e, he, h⟩ := List.mem_map.mp h
        cases h
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨e, he, rfl⟩
    have ho : (c, i) ∈ occurrences m := by simp [occurrences]
    simp only [Adj, edges, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨(c, i), ho, hm⟩)

def clauseRoute {n m : Nat} (c : Fin m) (i : Fin 3) : List (Vertex n m) :=
  (localOrder i).map (localEmbed c)

theorem clauseRoute_chain {n m : Nat} (φ : Formula n m) (c : Fin m) (i : Fin 3) :
    (clauseRoute c i).IsChain (Adj φ) :=
  List.isChain_map_of_isChain (localEmbed c) (fun _ _ h => localEmbed_adj φ c h)
    (localOrder_chain i)

def variableRoute {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool) (v : Fin n) :
    List (Vertex n m) :=
  [var v false] ++
    (if σ v then (occurrencesOf φ v).flatMap
      (fun o => XorGadget.leftVertices.map (PlanarSatAssembly.xor o)) else []) ++
    [var v true]

def order {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3) : List (Vertex n m) :=
  [sent 0, sent 1, sent 2] ++
    (List.finRange n).flatMap (variableRoute φ σ) ++
    (List.finRange m).flatMap (fun c => clauseRoute c (picked c))

theorem clauseRoute_count_sentinel {n m : Nat} (c : Fin m) (i : Fin 3) (v : Fin 3) :
    (clauseRoute (n := n) c i).count (sent v) = 0 := by
  apply List.count_eq_zero.mpr
  rintro hm
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
  cases u <;> simp [localEmbed, sent, clause, PlanarSatAssembly.xor] at hu

theorem clauseRoute_count_variable {n m : Nat} (c : Fin m) (i : Fin 3)
    (v : Fin n) (b : Bool) : (clauseRoute c i).count (var v b) = 0 := by
  apply List.count_eq_zero.mpr
  rintro hm
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
  cases u <;> simp [localEmbed, var, clause, PlanarSatAssembly.xor] at hu

theorem clauseRoute_count_clause {n m : Nat} (c d : Fin m) (i : Fin 3) (v : Fin 12) :
    (clauseRoute (n := n) c i).count (clause d v) = if c = d then 1 else 0 := by
  by_cases h : c = d
  · subst d
    change ((localOrder i).map (localEmbed c)).count (localEmbed c (Sum.inl v)) = _
    rw [List.count_map_of_injective _ _ (localEmbed_injective c)]
    simp [localOrder_count_clause]
  · rw [ite_eq_right h]
    apply List.count_eq_zero.mpr
    rintro hm
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases u <;> simp [localEmbed, clause, PlanarSatAssembly.xor, h] at hu

theorem clauseRoute_count_xor {n m : Nat} (c : Fin m) (i : Fin 3)
    (o : Occurrence m) (v : Fin 8) :
    (clauseRoute (n := n) c i).count (PlanarSatAssembly.xor o v) =
      if c = o.1 then (if i = o.2 then 0 else 1) else 0 := by
  rcases o with ⟨d, j⟩
  by_cases h : c = d
  · subst d
    change ((localOrder i).map (localEmbed c)).count (localEmbed c (Sum.inr (j, v))) = _
    rw [List.count_map_of_injective _ _ (localEmbed_injective c)]
    simp [localOrder_count_xor]
  · rw [ite_eq_right h]
    apply List.count_eq_zero.mpr
    rintro hm
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases u <;> simp [localEmbed, clause, PlanarSatAssembly.xor, h] at hu

theorem occurrences_count {m : Nat} (o : Occurrence m) : (occurrences m).count o = 1 := by
  rw [occurrences, List.count_flatMap]
  rw [List.sum_map_eq_nsmul_single o.1]
  · simp only [List.count_finRange, one_nsmul, Function.comp_apply]
    have hi : Function.Injective (fun j : Fin 3 => (o.1, j)) := by
      intro a b h
      exact (Prod.mk.inj h).2
    convert List.count_map_of_injective (List.finRange 3) _ hi o.2 using 1 <;> simp
  · intro c hc _
    apply List.count_eq_zero.mpr
    simp only [List.mem_map, List.mem_finRange, true_and, not_exists]
    intro j hj
    exact hc (congrArg Prod.fst hj)

theorem occurrencesOf_count {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) : (occurrencesOf φ v).count o = if φ o.1 o.2 = v then 1 else 0 := by
  by_cases h : φ o.1 o.2 = v
  · rw [ite_eq_left h, occurrencesOf, List.count_filter (by simpa using h), occurrences_count]
  · rw [ite_eq_right h]
    apply List.count_eq_zero.mpr
    simp [occurrencesOf, h]

theorem xorLeft_count {n m : Nat} (os : List (Occurrence m)) (o : Occurrence m) (v : Fin 8) :
    (os.flatMap (fun p => XorGadget.leftVertices.map (PlanarSatAssembly.xor (n := n) p))).count
      (PlanarSatAssembly.xor o v) = os.count o := by
  rw [List.count_flatMap, List.sum_map_eq_nsmul_single o]
  · simp only [Function.comp_apply,
      List.count_map_of_injective _ _ (xor_injective o), XorGadget.left_route_hamiltonian.2,
      nsmul_eq_mul, Nat.cast_id, Nat.mul_one]
  · intro p hp _
    apply List.count_eq_zero.mpr
    simp [PlanarSatAssembly.xor, List.mem_map, hp]

theorem variableRoute_count_xor {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (v : Fin n) (o : Occurrence m) (w : Fin 8) :
    (variableRoute φ σ v).count (PlanarSatAssembly.xor o w) =
      if σ v = true ∧ φ o.1 o.2 = v then 1 else 0 := by
  by_cases hv : σ v = true
  · simp only [variableRoute, hv, ite_true, List.count_append]
    rw [xorLeft_count, occurrencesOf_count]
    simp [var, PlanarSatAssembly.xor]
  · simp [variableRoute, hv, var, PlanarSatAssembly.xor]

private theorem left_count_zero {n m : Nat} (os : List (Occurrence m)) (v : Vertex n m)
    (h : ∀ o j, PlanarSatAssembly.xor o j ≠ v) :
    (os.flatMap (fun o => XorGadget.leftVertices.map (PlanarSatAssembly.xor o))).count v = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp hm
  obtain ⟨j, _, he⟩ := List.mem_map.mp ho
  exact h o j he

theorem variableRoute_count_sentinel {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (v : Fin n) (i : Fin 3) : (variableRoute φ σ v).count (sent i) = 0 := by
  have hz := left_count_zero (n := n) (occurrencesOf φ v) (sent i)
    (fun o j => by simp [PlanarSatAssembly.xor, sent])
  cases hv : σ v <;> simp only [variableRoute, hv, Bool.false_eq_true, ite_false, ite_true, List.count_append, hz]
  all_goals simp [var, sent]

theorem variableRoute_count_clause {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (v : Fin n) (c : Fin m) (i : Fin 12) : (variableRoute φ σ v).count (clause c i) = 0 := by
  have hz := left_count_zero (n := n) (occurrencesOf φ v) (clause c i)
    (fun o j => by simp [PlanarSatAssembly.xor, clause])
  cases hv : σ v <;> simp only [variableRoute, hv, Bool.false_eq_true, ite_false, ite_true, List.count_append, hz]
  all_goals simp [var, clause]

theorem variableRoute_count_variable {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (v w : Fin n) (b : Bool) : (variableRoute φ σ v).count (var w b) = if v = w then 1 else 0 := by
  have hz := left_count_zero (occurrencesOf φ v) (var w b)
    (fun o j => by simp [PlanarSatAssembly.xor, var])
  cases hv : σ v <;> simp only [variableRoute, hv, Bool.false_eq_true, ite_false, ite_true, List.count_append, hz]
  all_goals cases b <;> by_cases h : v = w <;> simp [List.count_cons, var, h]

theorem variableBlocks_count_xor {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (o : Occurrence m) (i : Fin 8) :
    ((List.finRange n).flatMap (variableRoute φ σ)).count (PlanarSatAssembly.xor o i) =
      if σ (φ o.1 o.2) = true then 1 else 0 := by
  rw [List.count_flatMap, List.sum_map_eq_nsmul_single (φ o.1 o.2)]
  · simp [variableRoute_count_xor]
  · intro v hv _
    simp [variableRoute_count_xor, Ne.symm hv]

theorem clauseBlocks_count_xor {n m : Nat} (picked : Fin m → Fin 3)
    (o : Occurrence m) (i : Fin 8) :
    ((List.finRange m).flatMap (fun c => clauseRoute (n := n) c (picked c))).count
      (PlanarSatAssembly.xor o i) = if picked o.1 = o.2 then 0 else 1 := by
  rw [List.count_flatMap, List.sum_map_eq_nsmul_single o.1]
  · simp [clauseRoute_count_xor]
  · intro c hc _
    simp [clauseRoute_count_xor, hc]

/-- Every actual graph vertex occurs exactly once when the chosen literal
of each clause agrees with the satisfying assignment. -/
theorem order_count_one {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3)
    (hpicked : ∀ c j, σ (φ c j) = true ↔ j = picked c) (v : Vertex n m) :
    (order φ σ picked).count v = 1 := by
  rcases v with i | ⟨v, b⟩ | ⟨c, i⟩ | ⟨o, i⟩
  · change (order φ σ picked).count (sent i) = 1
    simp only [order, List.count_append, List.count_flatMap, Function.comp_def,
      variableRoute_count_sentinel, clauseRoute_count_sentinel]
    fin_cases i <;> simp [sent]
  · change (order φ σ picked).count (var v b) = 1
    simp only [order, List.count_append, List.count_flatMap, Function.comp_def,
      variableRoute_count_variable, clauseRoute_count_variable]
    simp only [List.map_const', List.length_finRange, List.sum_replicate, nsmul_zero]
    rw [List.sum_map_eq_nsmul_single v]
    · simp [sent, var]
    · intro w hw _
      simp [hw]
  · change (order φ σ picked).count (clause c i) = 1
    simp only [order, List.count_append, List.count_flatMap, Function.comp_def,
      variableRoute_count_clause, clauseRoute_count_clause]
    simp only [List.map_const', List.length_finRange, List.sum_replicate, nsmul_zero]
    rw [List.sum_map_eq_nsmul_single c]
    · simp [sent, clause]
    · intro d hd _
      simp [hd]
  · change (order φ σ picked).count (PlanarSatAssembly.xor o i) = 1
    simp only [order, List.count_append]
    rw [variableBlocks_count_xor, clauseBlocks_count_xor]
    have hp := hpicked o.1 o.2
    by_cases he : picked o.1 = o.2
    · have ht := hp.mpr he.symm
      simp [sent, PlanarSatAssembly.xor, he, ht]
    · have ht : σ (φ o.1 o.2) ≠ true := fun h => he (hp.mp h).symm
      simp [sent, PlanarSatAssembly.xor, he, ht]

theorem order_nodup {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3)
    (hpicked : ∀ c j, σ (φ c j) = true ↔ j = picked c) :
    (order φ σ picked).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro v
  simp [order_count_one φ σ picked hpicked]

theorem order_covers {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3)
    (hpicked : ∀ c j, σ (φ c j) = true ↔ j = picked c) (v : Vertex n m) :
    v ∈ order φ σ picked := by
  apply List.count_pos_iff.mp
  simp [order_count_one φ σ picked hpicked]

theorem oneHot_iff : ∀ b : Fin 3 → Bool,
    ((List.finRange 3).filter b).length = 1 ↔ ∃ i, ∀ j, b j = true ↔ j = i := by decide

theorem exists_picked {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (h : Satisfies φ σ) : ∃ picked : Fin m → Fin 3,
      ∀ c j, σ (φ c j) = true ↔ j = picked c := by
  have hc : ∀ c, ∃ i, ∀ j, σ (φ c j) = true ↔ j = i := fun c =>
    (oneHot_iff (fun j => σ (φ c j))).mp (h c)
  choose picked hp using hc
  exact ⟨picked, hp⟩

end GridHardness.PlanarSatForward
