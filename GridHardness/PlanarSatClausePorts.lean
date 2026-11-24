/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatVariables

/-!
# Planar SAT Clause Ports

Identify the incoming and outgoing arcs at the ports of a clause gadget.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PlanarSatAssembly
open PlanarSatXor XorGadget

/-- At the right entry, the only predecessor outside an XOR is its clause bottom. -/
theorem xor_four_incoming {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (w : Vertex n m) (h : Adj φ w (xor o 4)) :
    w = xor o 5 ∨ w = clause o.1 (clauseBottom o.2) := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor,sent] at hs
  · exact False.elim (backbone_no_xor_target o 4 w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor,var] at hv
    · have := variableChain_xor_target φ v o 4 w hv
      contradiction
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges,xor,clause] at hc
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha
      rcases ha with ⟨hs,ht⟩ | ⟨_,ht⟩
      · have hao : o = a := by simpa [xor] using ht
        subst a
        exact Or.inr hs
      · simp [clause,xor] at ht
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor,Sum.inr.injEq,Prod.mk.injEq] at hdst
      rcases hdst with ⟨rfl,hdst⟩
      have hedge : ∀ e : Fin 10, (arc e).2 = 4 → (arc e).1 = 5 := by decide
      rw [hedge e hdst] at hsrc
      exact Or.inl hsrc.symm

/-- At the right exit, the only successor outside an XOR is its clause top. -/
theorem xor_seven_outgoing {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (w : Vertex n m) (h : Adj φ (xor o 7) w) :
    w = xor o 6 ∨ w = clause o.1 (clauseTop o.2) := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor,sent] at hs
  · exact False.elim (backbone_no_xor_source o 7 w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor,var] at hv
    · have := variableChain_xor_source φ v o 7 w hv
      contradiction
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges,xor,clause] at hc
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha
      rcases ha with ⟨hs,_⟩ | ⟨hs,ht⟩
      · simp [clause,xor] at hs
      · have hao : o = a := by simpa [xor] using hs
        subst a
        exact Or.inr ht
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor,Sum.inr.injEq,Prod.mk.injEq] at hsrc
      rcases hsrc with ⟨rfl,hsrc⟩
      have hedge : ∀ e : Fin 10, (arc e).1 = 7 → (arc e).2 = 6 := by decide
      rw [hedge e hsrc] at hdst
      exact Or.inl hdst.symm

/-- A right XOR traversal uses both actual clause links. -/
theorem rightRoute_clause_links {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ha : ∀ v, Adj φ v (succ v))
    (o : Occurrence m) (hr : selection succ (xor o) = rightRoute) :
    succ (clause o.1 (clauseBottom o.2)) = xor o 4 ∧
      succ (xor o 7) = clause o.1 (clauseTop o.2) := by
  have hn4 : succ (xor o 5) ≠ xor o 4 := by
    have := congrFun hr 6
    simpa [selection,arc,rightRoute] using this
  have hn7 : succ (xor o 7) ≠ xor o 6 := by
    have := congrFun hr 9
    simpa [selection,arc,rightRoute] using this
  constructor
  · have hap : Adj φ (succ.symm (xor o 4)) (xor o 4) := by
      simpa using ha (succ.symm (xor o 4))
    have he := xor_four_incoming φ o _ hap
    have hp : succ.symm (xor o 4) = clause o.1 (clauseBottom o.2) := by
      refine he.resolve_left ?_
      intro h
      have := congrArg succ h
      simp only [Equiv.apply_symm_apply] at this
      exact hn4 this.symm
    exact (congrArg succ hp).symm.trans (succ.apply_symm_apply _)
  · exact (xor_seven_outgoing φ o _ (ha (xor o 7))).resolve_left hn7

/-- The clause bottom takes its right branch exactly for the right XOR route. -/
theorem clause_bottom_right_iff {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ho : OneOrbit succ)
    (ha : ∀ v, Adj φ v (succ v)) (o : Occurrence m) :
    succ (clause o.1 (clauseBottom o.2)) = xor o 4 ↔
      selection succ (xor o) = rightRoute := by
  constructor
  · intro he
    rcases assembly_selection φ succ ho ha o with hl | hr
    · have hi : succ (xor o 5) = xor o 4 := by
        have := congrFun hl 6
        simpa [selection,arc,leftRoute] using this
      have := succ.injective (he.trans hi.symm)
      simp [clause,xor] at this
    · exact hr
  · exact fun hr => (rightRoute_clause_links φ succ ha o hr).1

private theorem backbone_no_clause_source {n m : Nat} (c : Fin m) (i : Fin 12)
    (hi : i ≠ 1) (v : Vertex n m) : (clause c i,v) ∉ backbone n m := by
  intro h
  have hm := (List.of_mem_zip h).1
  simp [slots,clause,sent,var] at hm
  exact hi hm.symm

private theorem backbone_no_clause_target {n m : Nat} (c : Fin m) (i : Fin 12)
    (hi : i ≠ 8) (v : Vertex n m) : (v,clause c i) ∉ backbone n m := by
  intro h
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append,List.mem_singleton] at hm
  rcases hm with hm | hm
  · have := List.mem_of_mem_tail hm
    simp [slots,clause,sent,var] at this
    exact hi this.symm
  · simp [clause,sent] at hm

/-- All actual outgoing edges of a clause, apart from its outer-backbone exit. -/
theorem clause_outgoing {n m : Nat} (φ : Formula n m) (c : Fin m)
    (i : Fin 12) (hi : i ≠ 1) (w : Vertex n m) (h : Adj φ (clause c i) w) :
    (∃ j, (i,j) ∈ clauseBody ∧ w = clause c j) ∨
      ∃ k, i = clauseBottom k ∧ w = xor (c,k) 4 := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [clause,sent] at hs
  · exact False.elim (backbone_no_clause_source c i hi w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [clause,var] at hv
    · have hm := (List.of_mem_zip hv).1
      simp [clause,var,xor] at hm
  · obtain ⟨d,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hc
    have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    simp only [clause,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at hs
    rcases hs with ⟨rfl,rfl⟩
    exact Or.inl ⟨b,hab,ht.symm⟩
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha
      rcases ha with ⟨hs,ht⟩ | ⟨hs,_⟩
      · have he : c = a.1 ∧ i = clauseBottom a.2 := by simpa [clause] using hs
        rcases a with ⟨d,k⟩
        simp only at he
        rcases he with ⟨rfl,hi⟩
        exact Or.inr ⟨k,hi,ht⟩
      · simp [clause,xor] at hs
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have hs := congrArg Prod.fst he
      simp [clause,xor] at hs

/-- All actual incoming edges of a clause, apart from its outer-backbone entry. -/
theorem clause_incoming {n m : Nat} (φ : Formula n m) (c : Fin m)
    (i : Fin 12) (hi : i ≠ 8) (w : Vertex n m) (h : Adj φ w (clause c i)) :
    (∃ j, (j,i) ∈ clauseBody ∧ w = clause c j) ∨
      ∃ k, i = clauseTop k ∧ w = xor (c,k) 7 := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [clause,sent] at hs
  · exact False.elim (backbone_no_clause_target c i hi w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [clause,var] at hv
    · have hm := (List.of_mem_zip hv).2
      simp [clause,var,xor] at hm
  · obtain ⟨d,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hc
    have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    simp only [clause,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at ht
    rcases ht with ⟨rfl,rfl⟩
    exact Or.inl ⟨a,hab,hs.symm⟩
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha
      rcases ha with ⟨_,ht⟩ | ⟨hs,ht⟩
      · simp [clause,xor] at ht
      · have he : c = a.1 ∧ i = clauseTop a.2 := by simpa [clause] using ht
        rcases a with ⟨d,k⟩
        simp only at he
        rcases he with ⟨rfl,hi⟩
        exact Or.inr ⟨k,hi,hs⟩
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have ht := congrArg Prod.snd he
      simp [clause,xor] at ht

def clauseSuccessors {n m : Nat} (c : Fin m) : Fin 12 → List (Vertex n m) :=
  ![[clause c 3,xor (c,0) 4], [], [clause c 1,clause c 3], [clause c 6],
    [clause c 7,xor (c,1) 4], [clause c 0], [clause c 5,clause c 7], [clause c 10],
    [clause c 11,xor (c,2) 4], [clause c 4], [clause c 9,clause c 11], [clause c 2]]

/-- A compact table of all successors available to the twelve actual clause vertices. -/
theorem clause_successor_mem {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ha : ∀ v, Adj φ v (succ v))
    (c : Fin m) (i : Fin 12) (hi : i ≠ 1) :
    succ (clause c i) ∈ clauseSuccessors c i := by
  rcases clause_outgoing φ c i hi _ (ha (clause c i)) with ⟨j,hij,he⟩ | ⟨k,hi,he⟩
  · rw [he]
    simp only [clauseBody,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hij
    rcases hij with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl,rfl⟩ <;> simp [clauseSuccessors]
  · rw [he,hi]
    fin_cases k <;> simp [clauseBottom,clauseSuccessors]

def clauseUpper : Fin 3 → Fin 12 := ![2,6,10]
def clauseLower : Fin 3 → Fin 12 := ![3,7,11]

/-- The two available bottom successors after connecting the occurrence XOR. -/
theorem clause_bottom_successors {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ha : ∀ v, Adj φ v (succ v))
    (c : Fin m) (j : Fin 3) :
    succ (clause c (clauseBottom j)) = clause c (clauseLower j) ∨
      succ (clause c (clauseBottom j)) = xor (c,j) 4 := by
  have h := clause_successor_mem φ succ ha c (clauseBottom j) (by fin_cases j <;> decide)
  fin_cases j <;> simpa [clauseSuccessors,clauseBottom,clauseLower] using h

/-- The two internal successors of each left upper vertex. -/
theorem clause_upper_successors {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ha : ∀ v, Adj φ v (succ v))
    (c : Fin m) (j : Fin 3) :
    succ (clause c (clauseUpper j)) = clause c (clauseTop j) ∨
      succ (clause c (clauseUpper j)) = clause c (clauseLower j) := by
  have h := clause_successor_mem φ succ ha c (clauseUpper j) (by fin_cases j <;> decide)
  fin_cases j <;> simpa [clauseSuccessors,clauseUpper,clauseLower,clauseTop] using h

/-- A clause top receives only its left upper edge or its occurrence's right exit. -/
theorem clause_top_incoming {n m : Nat} (φ : Formula n m) (c : Fin m)
    (j : Fin 3) (w : Vertex n m) (h : Adj φ w (clause c (clauseTop j))) :
    w = clause c (clauseUpper j) ∨ w = xor (c,j) 7 := by
  rcases clause_incoming φ c (clauseTop j) (by fin_cases j <;> decide) w h with
    ⟨k,hk,he⟩ | ⟨k,hk,he⟩
  · have hbody : ∀ j : Fin 3, ∀ k : Fin 12,
        (k,clauseTop j) ∈ clauseBody → k = clauseUpper j := by decide
    exact Or.inl ((hbody j k hk) ▸ he)
  · have hi : Function.Injective clauseTop := by decide
    have hjk := hi hk
    subst k
    exact Or.inr he

/-- The unselected truth value is exactly the XOR's right traversal. -/
theorem extractedAssignment_false_iff {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ho : OneOrbit succ)
    (ha : ∀ v, Adj φ v (succ v)) (o : Occurrence m) :
    extractedAssignment φ succ (φ o.1 o.2) = false ↔
      selection succ (xor o) = rightRoute := by
  have hne : leftRoute ≠ rightRoute := by decide
  constructor
  · intro hf
    rcases assembly_selection φ succ ho ha o with hl | hr
    · have ht := (extractedAssignment_spec φ succ ho ha o).mpr hl
      simp [hf] at ht
    · exact hr
  · intro hr
    cases ht : extractedAssignment φ succ (φ o.1 o.2) with
    | false => rfl
    | true =>
      have hl := (extractedAssignment_spec φ succ ho ha o).mp ht
      exact False.elim (hne (hl.symm.trans hr))

/-- Actual clause-bottom successor as a function of the extracted truth value. -/
theorem clause_bottom_step {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ho : OneOrbit succ)
    (ha : ∀ v, Adj φ v (succ v)) (c : Fin m) (j : Fin 3) :
    succ (clause c (clauseBottom j)) =
      if extractedAssignment φ succ (φ c j) then clause c (clauseLower j) else xor (c,j) 4 := by
  cases ht : extractedAssignment φ succ (φ c j) with
  | false =>
    exact (rightRoute_clause_links φ succ ha (c,j)
      ((extractedAssignment_false_iff φ succ ho ha (c,j)).mp ht)).1
  | true =>
    have hl := (extractedAssignment_spec φ succ ho ha (c,j)).mp ht
    have hne : succ (clause c (clauseBottom j)) ≠ xor (c,j) 4 := by
      intro hb
      have hr := (clause_bottom_right_iff φ succ ho ha (c,j)).mp hb
      have : leftRoute ≠ rightRoute := by decide
      exact this (hl.symm.trans hr)
    exact (clause_bottom_successors φ succ ha c j).resolve_right hne

/-- The corresponding upper successor is forced by the single-predecessor condition. -/
theorem clause_upper_step {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (ho : OneOrbit succ)
    (ha : ∀ v, Adj φ v (succ v)) (c : Fin m) (j : Fin 3) :
    succ (clause c (clauseUpper j)) =
      if extractedAssignment φ succ (φ c j) then clause c (clauseTop j) else clause c (clauseLower j) := by
  cases ht : extractedAssignment φ succ (φ c j) with
  | false =>
    have hr := (extractedAssignment_false_iff φ succ ho ha (c,j)).mp ht
    have he := (rightRoute_clause_links φ succ ha (c,j) hr).2
    have hne : succ (clause c (clauseUpper j)) ≠ clause c (clauseTop j) := by
      intro hu
      have := succ.injective (hu.trans he.symm)
      simp [clause,xor] at this
    exact (clause_upper_successors φ succ ha c j).resolve_left hne
  | true =>
    have hl := (extractedAssignment_spec φ succ ho ha (c,j)).mp ht
    have he : succ (xor (c,j) 7) = xor (c,j) 6 := by
      have := congrFun hl 9
      simpa [selection,arc,leftRoute] using this
    have hpred := clause_top_incoming φ c j (succ.symm (clause c (clauseTop j)))
      (by simpa using ha (succ.symm (clause c (clauseTop j))))
    have hp : succ.symm (clause c (clauseTop j)) = clause c (clauseUpper j) := by
      refine hpred.resolve_right ?_
      intro hx
      have := congrArg succ hx
      simp only [Equiv.apply_symm_apply,he] at this
      simp [clause,xor] at this
    exact (congrArg succ hp).symm.trans (succ.apply_symm_apply _)

end GridHardness.PlanarSatAssembly
