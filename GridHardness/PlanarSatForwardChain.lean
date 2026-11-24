/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatForward

/-!
# Planar SAT Forward Chain

Construction of the traversal chains for a variable and its XOR ports.
-/

@[expose] public section

namespace GridHardness.PlanarSatForward
open PlanarSatAssembly

/-- Splicing nonempty directed paths into a chain preserves every link.
The link list contains no fresh junction vertices. -/
theorem chain_splice {I V : Type*} (D : V → V → Prop)
    (body : I → List V) (entry exit : I → V)
    (hbody : ∀ i, (body i).IsChain D)
    (hhead : ∀ i, (body i).head? = some (entry i))
    (hlast : ∀ i, (body i).getLast? = some (exit i))
    (is : List I) (a b : V)
    (hlink : ∀ u v, (u, v) ∈ (a :: is.map exit).zip (is.map entry ++ [b]) → D u v) :
    ([a] ++ is.flatMap body ++ [b]).IsChain D := by
  induction is generalizing a with
  | nil => simpa using hlink a b (by simp)
  | cons i is ih =>
      have hab : D a (entry i) := hlink a (entry i) (by simp)
      have hr := ih (exit i) (fun u v hv => hlink u v (by simp [hv]))
      have hi : ([a] ++ body i).IsChain D := by
        apply (List.IsChain.singleton a).append (hbody i)
        intro x hx y hy
        have hx' : x = a := by simpa [eq_comm] using hx
        have hy' : y = entry i := by simpa [hhead i,eq_comm] using hy
        simpa [hx', hy'] using hab
      obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp (hlast i)
      have hi' : (([a] ++ pre) ++ [exit i]).IsChain D := by simpa [hpre] using hi
      have hr' : ([exit i] ++ (is.flatMap body ++ [b])).IsChain D := by
        simpa only [List.append_assoc] using hr
      have hh := hi'.append_overlap hr' (by simp)
      simpa [hpre, List.append_assoc] using hh

theorem xorLeft_chain {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    (XorGadget.leftVertices.map (PlanarSatAssembly.xor o)).IsChain (Adj φ) := by
  apply List.isChain_map_of_isChain _ _ XorGadget.left_route_hamiltonian.1
  intro a b h
  obtain ⟨e, _, he⟩ := h
  have hx : (PlanarSatAssembly.xor (n := n) o a, PlanarSatAssembly.xor o b) ∈ xorEdges o := by
    apply List.mem_map.mpr
    exact ⟨e, List.mem_finRange e, by simp [he]⟩
  have ho : o ∈ occurrences m := by rcases o with ⟨c, i⟩; simp [occurrences]
  simp only [Adj, edges, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨o, ho, List.mem_append_right _ hx⟩)

theorem variableRoute_chain {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool) (v : Fin n) :
    (variableRoute φ σ v).IsChain (Adj φ) := by
  have hmem : ∀ p ∈ (var v false, var v true) :: variableChain φ v,
      p ∈ edges φ := by
    intro p hp
    simp only [edges, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨v, List.mem_finRange v, hp⟩)))
  cases hv : σ v
  · simpa [variableRoute, hv,Adj] using hmem (var v false, var v true) (by simp)
  · simp only [variableRoute, hv, ite_true]
    apply chain_splice (Adj φ)
      (fun o => XorGadget.leftVertices.map (PlanarSatAssembly.xor o))
      (fun o => PlanarSatAssembly.xor o 3) (fun o => PlanarSatAssembly.xor o 0)
      (xorLeft_chain φ)
      (fun o => by rfl) (fun o => by rfl)
    intro u w h
    exact hmem (u, w) (List.mem_cons_of_mem _ h)

theorem variableRoute_head {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool) (v : Fin n) :
    (variableRoute φ σ v).head? = some (var v false) := by
  simp [variableRoute]

theorem variableRoute_last {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool) (v : Fin n) :
    (variableRoute φ σ v).getLast? = some (var v true) := by
  simp only [variableRoute,List.getLast?_append]
  rfl

theorem clauseRoute_head {n m : Nat} (c : Fin m) (i : Fin 3) :
    (clauseRoute (n := n) c i).head? = some (clause c 8) := by
  simp [clauseRoute, List.head?_map, localOrder_head, localEmbed]

theorem clauseRoute_last {n m : Nat} (c : Fin m) (i : Fin 3) :
    (clauseRoute (n := n) c i).getLast? = some (clause c 1) := by
  simp [clauseRoute, List.getLast?_map, localOrder_last, localEmbed]

abbrev Block (n m : Nat) := Option (Fin n ⊕ Fin m)

def blockBody {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3) : Block n m → List (Vertex n m)
  | none => [sent 1,sent 2]
  | some (.inl v) => variableRoute φ σ v
  | some (.inr c) => clauseRoute c (picked c)

def blockEntry {n m : Nat} : Block n m → Vertex n m
  | none => sent 1
  | some (.inl v) => var v false
  | some (.inr c) => clause c 8

def blockExit {n m : Nat} : Block n m → Vertex n m
  | none => sent 2
  | some (.inl v) => var v true
  | some (.inr c) => clause c 1

def blocks (n m : Nat) : List (Block n m) :=
  none :: ((List.finRange n).map (some ∘ Sum.inl) ++ (List.finRange m).map (some ∘ Sum.inr))

/-- Every block's two boundary labels agree with the backbone constructor. -/
theorem block_links (n m : Nat) :
    ((sent 0 : Vertex n m) :: (blocks n m).map blockExit).zip
      ((blocks n m).map blockEntry ++ [sent 0]) =
        (sent 0,sent 1) :: backbone n m := by
  simp [blocks,blockEntry,blockExit,backbone,slots,List.map_append,List.map_map,
    Function.comp_def,List.append_assoc]

/-- The explicitly written order, including its closing edge, follows the actual graph.
This holds for every assignment and chosen clause route; satisfaction is needed
separately to show that every vertex occurs exactly once. -/
theorem order_closed_chain {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3) : (order φ σ picked ++ [sent 0]).IsChain (Adj φ) := by
  have hbody : ∀ i, (blockBody φ σ picked i).IsChain (Adj φ) := by
    intro i
    cases i with
    | none => simp [blockBody,Adj,edges]
    | some i =>
      cases i with
      | inl v => exact variableRoute_chain φ σ v
      | inr c => exact clauseRoute_chain φ c (picked c)
  have hhead : ∀ i, (blockBody φ σ picked i).head? = some (blockEntry i) := by
    intro i
    cases i with
    | none => rfl
    | some i =>
      cases i with
      | inl v => exact variableRoute_head φ σ v
      | inr c => exact clauseRoute_head c (picked c)
  have hlast : ∀ i, (blockBody φ σ picked i).getLast? = some (blockExit i) := by
    intro i
    cases i with
    | none => rfl
    | some i =>
      cases i with
      | inl v => exact variableRoute_last φ σ v
      | inr c => exact clauseRoute_last c (picked c)
  have h := chain_splice (Adj φ) (blockBody φ σ picked) blockEntry blockExit
    hbody hhead hlast (blocks n m) (sent 0) (sent 0) ?_
  · simpa [blocks,blockBody,order,List.flatMap_append,List.flatMap_map,
      Function.comp_def,List.append_assoc] using h
  · intro u v hlink
    rw [block_links] at hlink
    rcases List.mem_cons.mp hlink with he | he
    · have hu := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      simp only at hu hv
      subst u; subst v
      simp [Adj,edges]
    · simp only [Adj,edges,List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr he)))

/-- Consecutive vertices of the proposed global Hamiltonian witness are adjacent. -/
theorem order_chain {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3) : (order φ σ picked).IsChain (Adj φ) :=
  (List.isChain_append.mp (order_closed_chain φ σ picked)).1

/-- The final vertex links back to the first sentinel. -/
theorem order_closing_edge {n m : Nat} (φ : Formula n m) (σ : Fin n → Bool)
    (picked : Fin m → Fin 3) :
    ∀ v ∈ (order φ σ picked).getLast?, Adj φ v (sent 0) := by
  intro v hv
  exact (List.isChain_append.mp (order_closed_chain φ σ picked)).2.2 v hv (sent 0) (by simp)

end GridHardness.PlanarSatForward
