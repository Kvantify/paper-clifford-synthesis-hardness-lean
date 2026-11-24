/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatClausePorts

/-!
# Planar SAT Degree

Prove uniqueness of the attachment arcs at the ports of the SAT graph.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PlanarSatAssembly

private theorem vars_nodup (n m : Nat) (b : Bool) :
    ((List.finRange n).map (fun v => var (m := m) v b)).Nodup := by
  apply (List.nodup_finRange n).map
  intro u v h
  simpa [var] using h

private theorem clauses_nodup (n m : Nat) (i : Fin 12) :
    ((List.finRange m).map (fun c => clause (n := n) c i)).Nodup := by
  apply (List.nodup_finRange m).map
  intro u v h
  simpa [clause] using h

theorem slots_exit_nodup (n m : Nat) : ((slots n m).map Prod.snd).Nodup := by
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  apply List.nodup_cons.mpr
  constructor
  · simp [sent,var,clause]
  · apply List.nodup_append.mpr
    refine ⟨vars_nodup n m true,clauses_nodup n m 1,?_⟩
    intro a ha b hb hab
    obtain ⟨v,_,hv⟩ := List.mem_map.mp ha
    obtain ⟨c,_,hc⟩ := List.mem_map.mp hb
    have := hv.trans (hab.trans hc.symm)
    simp [var,clause] at this

theorem slots_entry_nodup (n m : Nat) : ((slots n m).map Prod.fst).Nodup := by
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  apply List.nodup_cons.mpr
  constructor
  · simp [sent,var,clause]
  · apply List.nodup_append.mpr
    refine ⟨vars_nodup n m false,clauses_nodup n m 8,?_⟩
    intro a ha b hb hab
    obtain ⟨v,_,hv⟩ := List.mem_map.mp ha
    obtain ⟨c,_,hc⟩ := List.mem_map.mp hb
    have := hv.trans (hab.trans hc.symm)
    simp [var,clause] at this

/-- The outer backbone is a partial function: no vertex has two backbone successors. -/
theorem backbone_target_unique {n m : Nat} {a b c : Vertex n m}
    (hb : (a, b) ∈ backbone n m) (hc : (a, c) ∈ backbone n m) : b = c := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hb
  obtain ⟨j,hj,hf⟩ := List.getElem_of_mem hc
  simp only [backbone,List.getElem_zip] at he hf
  have hij : i = j := (slots_exit_nodup n m).getElem_inj_iff.mp
    ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)
  subst j
  exact (congrArg Prod.snd he).symm.trans (congrArg Prod.snd hf)

/-- Likewise no vertex has two predecessors on the outer backbone. -/
theorem backbone_source_unique {n m : Nat} {a b c : Vertex n m}
    (ha : (a, c) ∈ backbone n m) (hb : (b, c) ∈ backbone n m) : a = b := by
  have hn : (((slots n m).map Prod.fst).tail ++ [sent 0]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(slots_entry_nodup n m).tail,by simp,?_⟩
    intro x hx y hy hxy
    have hy' : y = sent (n := n) (m := m) 0 := by simpa using hy
    have hxs : x = sent (n := n) (m := m) 0 := hxy.trans hy'
    rw [hxs] at hx
    simpa [slots,sent,var,clause] using hx
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
  obtain ⟨j,hj,hf⟩ := List.getElem_of_mem hb
  simp only [backbone,List.getElem_zip] at he hf
  have hij : i = j := hn.getElem_inj_iff.mp
    ((congrArg Prod.snd he).trans (congrArg Prod.snd hf).symm)
  subst j
  exact (congrArg Prod.fst he).symm.trans (congrArg Prod.fst hf)

private def variableSourceOwner {n m : Nat} (φ : Formula n m) : Vertex n m → Option (Fin n)
  | .inr (.inl (v,false)) => some v
  | .inr (.inr (.inr (o,i))) => if i = 0 then some (φ o.1 o.2) else none
  | _ => none

private def variableTargetOwner {n m : Nat} (φ : Formula n m) : Vertex n m → Option (Fin n)
  | .inr (.inl (v,true)) => some v
  | .inr (.inr (.inr (o,i))) => if i = 3 then some (φ o.1 o.2) else none
  | _ => none

private theorem source_owner {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b : Vertex n m} (h : (a, b) ∈ variableChain φ v) : variableSourceOwner φ a = some v := by
  have hm := (List.of_mem_zip h).1
  simp only [List.mem_cons,List.mem_map] at hm
  rcases hm with rfl | ⟨o,ho,rfl⟩
  · rfl
  · have hv := (mem_occurrencesOf φ v o).mp ho
    simp [variableSourceOwner,xor,hv]

private theorem target_owner {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b : Vertex n m} (h : (a, b) ∈ variableChain φ v) : variableTargetOwner φ b = some v := by
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hm
  rcases hm with ⟨o,ho,rfl⟩ | rfl
  · have hv := (mem_occurrencesOf φ v o).mp ho
    simp [variableTargetOwner,xor,hv]
  · rfl

/-- Even across distinct variable lists, every external source has a unique successor. -/
theorem variableChains_target_unique {n m : Nat} (φ : Formula n m)
    (v w : Fin n) {a b c : Vertex n m}
    (hb : (a, b) ∈ variableChain φ v) (hc : (a, c) ∈ variableChain φ w) : b = c := by
  have hvw := Option.some.inj ((source_owner φ v hb).symm.trans (source_owner φ w hc))
  subst w
  exact variableChain_target_unique φ v hb hc

/-- Distinct variable lists cannot give the same target two predecessors. -/
theorem variableChains_source_unique {n m : Nat} (φ : Formula n m)
    (v w : Fin n) {a b c : Vertex n m}
    (ha : (a, c) ∈ variableChain φ v) (hb : (b, c) ∈ variableChain φ w) : a = b := by
  have hvw := Option.some.inj ((target_owner φ v ha).symm.trans (target_owner φ w hb))
  subst w
  exact variableChain_source_unique φ v ha hb

/-- Clause-link sources are unique across all occurrences. -/
theorem clauseLinks_target_unique {n m : Nat} (o p : Occurrence m)
    {a b c : Vertex n m} (hb : (a, b) ∈ clauseLinks o) (hc : (a, c) ∈ clauseLinks p) : b = c := by
  simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hb hc
  rcases hb with ⟨hb1,hb2⟩ | ⟨hb1,hb2⟩ <;>
    rcases hc with ⟨hc1,hc2⟩ | ⟨hc1,hc2⟩
  · have h := hb1.symm.trans hc1
    have hi : Function.Injective clauseBottom := by decide
    have hpairs : o.1 = p.1 ∧ clauseBottom o.2 = clauseBottom p.2 := by simpa [clause] using h
    have he : o = p := Prod.ext hpairs.1 (hi hpairs.2)
    subst p
    exact hb2.trans hc2.symm
  · have := hb1.symm.trans hc1
    simp [clause,xor] at this
  · have := hb1.symm.trans hc1
    simp [clause,xor] at this
  · have he : o = p := by simpa [xor] using hb1.symm.trans hc1
    subst p
    exact hb2.trans hc2.symm

private def outgoingRole {n m : Nat} : Vertex n m → Fin 3
  | .inl _ => 0
  | .inr (.inl (_,b)) => if b then 0 else 1
  | .inr (.inr (.inl (_,i))) => if i = 1 then 0 else 2
  | .inr (.inr (.inr (_,i))) => if i = 0 then 1 else 2

private theorem backbone_outgoingRole {n m : Nat} {a b : Vertex n m}
    (h : (a, b) ∈ backbone n m) : outgoingRole a = 0 := by
  have hm := (List.of_mem_zip h).1
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hm
  rcases hm with (rfl | ⟨v,_,rfl⟩) | ⟨c,_,rfl⟩ <;> rfl

private theorem variableChain_outgoingRole {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b : Vertex n m} (h : (a, b) ∈ variableChain φ v) : outgoingRole a = 1 := by
  have hm := (List.of_mem_zip h).1
  simp only [List.mem_cons,List.mem_map] at hm
  rcases hm with rfl | ⟨o,_,rfl⟩ <;> rfl

private theorem clauseLinks_outgoingRole {n m : Nat} (o : Occurrence m)
    {a b : Vertex n m} (h : (a, b) ∈ clauseLinks o) : outgoingRole a = 2 := by
  rcases List.mem_cons.mp h with h | h
  · have ha := congrArg Prod.fst h
    change a = clause o.1 (clauseBottom o.2) at ha
    rw [ha]
    rcases o with ⟨c,j⟩
    fin_cases j <;> rfl
  · have h := List.mem_singleton.mp h
    have ha := congrArg Prod.fst h
    change a = xor o 7 at ha
    rw [ha]
    rfl

/-- All links joining distinct blocks of the construction. -/
def External {n m : Nat} (φ : Formula n m) (a b : Vertex n m) : Prop :=
  (a,b) ∈ backbone n m ∨ (∃ v, (a,b) ∈ variableChain φ v) ∨ ∃ o, (a,b) ∈ clauseLinks o

/-- Every inter-block source has at most one external successor. -/
theorem external_target_unique {n m : Nat} (φ : Formula n m) {a b c : Vertex n m}
    (hb : External φ a b) (hc : External φ a c) : b = c := by
  rcases hb with hb | ⟨v,hb⟩ | ⟨o,hb⟩ <;>
    rcases hc with hc | ⟨w,hc⟩ | ⟨p,hc⟩
  · exact backbone_target_unique hb hc
  · have h := (backbone_outgoingRole hb).symm.trans (variableChain_outgoingRole φ w hc)
    contradiction
  · have h := (backbone_outgoingRole hb).symm.trans (clauseLinks_outgoingRole p hc)
    contradiction
  · have h := (variableChain_outgoingRole φ v hb).symm.trans (backbone_outgoingRole hc)
    contradiction
  · exact variableChains_target_unique φ v w hb hc
  · have h := (variableChain_outgoingRole φ v hb).symm.trans (clauseLinks_outgoingRole p hc)
    contradiction
  · have h := (clauseLinks_outgoingRole o hb).symm.trans (backbone_outgoingRole hc)
    contradiction
  · have h := (clauseLinks_outgoingRole o hb).symm.trans (variableChain_outgoingRole φ w hc)
    contradiction
  · exact clauseLinks_target_unique o p hb hc

def clauseInternal : Fin 12 → List (Fin 12) :=
  ![[3],[],[1,3],[6],[7],[0],[5,7],[10],[11],[4],[9,11],[2]]

def xorInternal : Fin 8 → List (Fin 8) := ![[1],[5],[1,3],[7],[0],[4,6],[2],[6]]

/-- The internal successor lists, before the three kinds of external links are joined. -/
def internalSuccessors {n m : Nat} : Vertex n m → List (Vertex n m)
  | .inl i => ![[sent 1],[sent 2],[]] i
  | .inr (.inl (v,b)) => if b then [] else [var v true]
  | .inr (.inr (.inl (c,i))) => (clauseInternal i).map (clause c)
  | .inr (.inr (.inr (o,i))) => (xorInternal i).map (xor o)

private theorem internal_length_le_two {n m : Nat} (a : Vertex n m) :
    (internalSuccessors a).length ≤ 2 := by
  rcases a with i | (⟨v,b⟩ | (⟨c,i⟩ | ⟨o,i⟩))
  · fin_cases i <;> simp [internalSuccessors]
  · cases b <;> simp [internalSuccessors]
  · fin_cases i <;> simp [internalSuccessors,clauseInternal]
  · fin_cases i <;> simp [internalSuccessors,xorInternal]

private theorem internal_length_of_role {n m : Nat} (a : Vertex n m)
    (h : outgoingRole a ≠ 2) : (internalSuccessors a).length ≤ 1 := by
  rcases a with i | (⟨v,b⟩ | (⟨c,i⟩ | ⟨o,i⟩))
  · fin_cases i <;> simp [internalSuccessors]
  · cases b <;> simp [internalSuccessors]
  · fin_cases i <;> simp_all [internalSuccessors,clauseInternal,outgoingRole]
  · fin_cases i <;> simp_all [internalSuccessors,xorInternal,outgoingRole]

private theorem internal_length_of_external {n m : Nat} (φ : Formula n m)
    {a b : Vertex n m} (h : External φ a b) : (internalSuccessors a).length ≤ 1 := by
  rcases h with hb | ⟨v,hv⟩ | ⟨o,ho⟩
  · apply internal_length_of_role
    rw [backbone_outgoingRole hb]
    decide
  · apply internal_length_of_role
    rw [variableChain_outgoingRole φ v hv]
    decide
  · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ho
    rcases ho with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · rcases o with ⟨c,j⟩
      fin_cases j <;> simp [internalSuccessors,clause,clauseBottom,clauseInternal]
    · simp [internalSuccessors,xor,xorInternal]

/-- Every actual successor is one of the small internal list or its unique external link. -/
theorem outgoing_internal_or_external {n m : Nat} (φ : Formula n m)
    {a b : Vertex n m} (h : Adj φ a b) : b ∈ internalSuccessors a ∨ External φ a b := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hs
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [internalSuccessors,sent]
  · exact Or.inr (Or.inl hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with he | he
    · cases he
      exact Or.inl (by simp [internalSuccessors,var])
    · exact Or.inr (Or.inr (Or.inl ⟨v,he⟩))
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨i,j⟩,hij,he⟩ := List.mem_map.mp hc
    cases he
    apply Or.inl
    have hbody : ∀ i j : Fin 12, (i,j) ∈ clauseBody → j ∈ clauseInternal i := by decide
    exact List.mem_map.mpr ⟨j,hbody i j hij,rfl⟩
  · obtain ⟨o,_,ho⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ho with he | he
    · exact Or.inr (Or.inr (Or.inr ⟨o,he⟩))
    · obtain ⟨e,_,he⟩ := List.mem_map.mp he
      cases he
      apply Or.inl
      have hedge : ∀ e : Fin 10, (XorGadget.arc e).2 ∈ xorInternal (XorGadget.arc e).1 := by decide
      exact List.mem_map.mpr ⟨(XorGadget.arc e).2,hedge e,rfl⟩

/-- Every assembled vertex has directed out-degree at most two. -/
theorem outdegree_le_two {n m : Nat} (φ : Formula n m) (a : Vertex n m) :
    (Finset.univ.filter (fun b => Adj φ a b)).card ≤ 2 := by
  classical
  by_cases he : ∃ b, External φ a b
  · obtain ⟨b,hb⟩ := he
    have hsub : Finset.univ.filter (fun c => Adj φ a c) ⊆
        (internalSuccessors a).toFinset ∪ {b} := by
      intro c hc
      rcases outgoing_internal_or_external φ (Finset.mem_filter.mp hc).2 with hc | hc
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hc)
      · exact Finset.mem_union_right _ (by simpa using external_target_unique φ hc hb)
    have hi := (List.toFinset_card_le (internalSuccessors a)).trans (internal_length_of_external φ hb)
    calc
      _ ≤ ((internalSuccessors a).toFinset ∪ {b}).card := Finset.card_le_card hsub
      _ ≤ (internalSuccessors a).toFinset.card + 1 := by simpa using Finset.card_union_le (internalSuccessors a).toFinset {b}
      _ ≤ 2 := by omega
  · have hsub : Finset.univ.filter (fun c => Adj φ a c) ⊆ (internalSuccessors a).toFinset := by
      intro c hc
      rcases outgoing_internal_or_external φ (Finset.mem_filter.mp hc).2 with hc | hc
      · exact List.mem_toFinset.mpr hc
      · exact False.elim (he ⟨c,hc⟩)
    exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (internal_length_le_two a))

/-- Clause-link targets are unique across all occurrences. -/
theorem clauseLinks_source_unique {n m : Nat} (o p : Occurrence m)
    {a b c : Vertex n m} (ha : (a, c) ∈ clauseLinks o) (hb : (b, c) ∈ clauseLinks p) : a = b := by
  simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ha hb
  rcases ha with ⟨ha1,ha2⟩ | ⟨ha1,ha2⟩ <;>
    rcases hb with ⟨hb1,hb2⟩ | ⟨hb1,hb2⟩
  · have he : o = p := by simpa [xor] using ha2.symm.trans hb2
    subst p
    exact ha1.trans hb1.symm
  · have := ha2.symm.trans hb2
    simp [clause,xor] at this
  · have := ha2.symm.trans hb2
    simp [clause,xor] at this
  · have hi : Function.Injective clauseTop := by decide
    have hpairs : o.1 = p.1 ∧ clauseTop o.2 = clauseTop p.2 := by
      simpa [clause] using ha2.symm.trans hb2
    have he : o = p := Prod.ext hpairs.1 (hi hpairs.2)
    subst p
    exact ha1.trans hb1.symm

private def incomingRole {n m : Nat} : Vertex n m → Fin 3
  | .inl _ => 0
  | .inr (.inl (_,b)) => if b then 1 else 0
  | .inr (.inr (.inl (_,i))) => if i = 8 then 0 else 2
  | .inr (.inr (.inr (_,i))) => if i = 3 then 1 else 2

private theorem backbone_incomingRole {n m : Nat} {a b : Vertex n m}
    (h : (a, b) ∈ backbone n m) : incomingRole b = 0 := by
  have hm := (List.of_mem_zip h).2
  rcases List.mem_append.mp hm with hm | hm
  · have ht := List.mem_of_mem_tail hm
    simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at ht
    rcases ht with (rfl | ⟨v,_,rfl⟩) | ⟨c,_,rfl⟩ <;> rfl
  · have := List.mem_singleton.mp hm
    subst b
    rfl

private theorem variableChain_incomingRole {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b : Vertex n m} (h : (a, b) ∈ variableChain φ v) : incomingRole b = 1 := by
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hm
  rcases hm with ⟨o,_,rfl⟩ | rfl <;> rfl

private theorem clauseLinks_incomingRole {n m : Nat} (o : Occurrence m)
    {a b : Vertex n m} (h : (a, b) ∈ clauseLinks o) : incomingRole b = 2 := by
  rcases List.mem_cons.mp h with h | h
  · have hb := congrArg Prod.snd h
    change b = xor o 4 at hb
    rw [hb]
    rfl
  · have h := List.mem_singleton.mp h
    have hb := congrArg Prod.snd h
    change b = clause o.1 (clauseTop o.2) at hb
    rw [hb]
    rcases o with ⟨c,j⟩
    fin_cases j <;> rfl

/-- Every inter-block target has at most one external predecessor. -/
theorem external_source_unique {n m : Nat} (φ : Formula n m) {a b c : Vertex n m}
    (ha : External φ a c) (hb : External φ b c) : a = b := by
  rcases ha with ha | ⟨v,ha⟩ | ⟨o,ha⟩ <;>
    rcases hb with hb | ⟨w,hb⟩ | ⟨p,hb⟩
  · exact backbone_source_unique ha hb
  · have h := (backbone_incomingRole ha).symm.trans (variableChain_incomingRole φ w hb)
    contradiction
  · have h := (backbone_incomingRole ha).symm.trans (clauseLinks_incomingRole p hb)
    contradiction
  · have h := (variableChain_incomingRole φ v ha).symm.trans (backbone_incomingRole hb)
    contradiction
  · exact variableChains_source_unique φ v w ha hb
  · have h := (variableChain_incomingRole φ v ha).symm.trans (clauseLinks_incomingRole p hb)
    contradiction
  · have h := (clauseLinks_incomingRole o ha).symm.trans (backbone_incomingRole hb)
    contradiction
  · have h := (clauseLinks_incomingRole o ha).symm.trans (variableChain_incomingRole φ w hb)
    contradiction
  · exact clauseLinks_source_unique o p ha hb

def clausePredecessors : Fin 12 → List (Fin 12) :=
  ![[5],[2],[11],[0,2],[9],[6],[3],[4,6],[],[10],[7],[8,10]]

def xorPredecessors : Fin 8 → List (Fin 8) := ![[4],[0,2],[6],[2],[5],[1],[5,7],[3]]

def internalPredecessors {n m : Nat} : Vertex n m → List (Vertex n m)
  | .inl i => ![[],[sent 0],[sent 1]] i
  | .inr (.inl (v,b)) => if b then [var v false] else []
  | .inr (.inr (.inl (c,i))) => (clausePredecessors i).map (clause c)
  | .inr (.inr (.inr (o,i))) => (xorPredecessors i).map (xor o)

private theorem internal_predecessor_length_le_two {n m : Nat} (a : Vertex n m) :
    (internalPredecessors a).length ≤ 2 := by
  rcases a with i | (⟨v,b⟩ | (⟨c,i⟩ | ⟨o,i⟩))
  · fin_cases i <;> simp [internalPredecessors]
  · cases b <;> simp [internalPredecessors]
  · fin_cases i <;> simp [internalPredecessors,clausePredecessors]
  · fin_cases i <;> simp [internalPredecessors,xorPredecessors]

private theorem internal_predecessor_length_of_role {n m : Nat} (a : Vertex n m)
    (h : incomingRole a ≠ 2) : (internalPredecessors a).length ≤ 1 := by
  rcases a with i | (⟨v,b⟩ | (⟨c,i⟩ | ⟨o,i⟩))
  · fin_cases i <;> simp [internalPredecessors]
  · cases b <;> simp [internalPredecessors]
  · fin_cases i <;> simp_all [internalPredecessors,clausePredecessors,incomingRole]
  · fin_cases i <;> simp_all [internalPredecessors,xorPredecessors,incomingRole]

private theorem internal_predecessor_length_of_external {n m : Nat} (φ : Formula n m)
    {a b : Vertex n m} (h : External φ a b) : (internalPredecessors b).length ≤ 1 := by
  rcases h with hb | ⟨v,hv⟩ | ⟨o,ho⟩
  · apply internal_predecessor_length_of_role
    rw [backbone_incomingRole hb]
    decide
  · apply internal_predecessor_length_of_role
    rw [variableChain_incomingRole φ v hv]
    decide
  · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at ho
    rcases ho with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · simp [internalPredecessors,xor,xorPredecessors]
    · rcases o with ⟨c,j⟩
      fin_cases j <;> simp [internalPredecessors,clause,clauseTop,clausePredecessors]

/-- The incoming counterpart of the actual successor decomposition. -/
theorem incoming_internal_or_external {n m : Nat} (φ : Formula n m)
    {a b : Vertex n m} (h : Adj φ a b) : a ∈ internalPredecessors b ∨ External φ a b := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hs
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [internalPredecessors,sent]
  · exact Or.inr (Or.inl hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with he | he
    · cases he
      exact Or.inl (by simp [internalPredecessors,var])
    · exact Or.inr (Or.inr (Or.inl ⟨v,he⟩))
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨i,j⟩,hij,he⟩ := List.mem_map.mp hc
    cases he
    apply Or.inl
    have hbody : ∀ i j : Fin 12, (i,j) ∈ clauseBody → i ∈ clausePredecessors j := by decide
    exact List.mem_map.mpr ⟨i,hbody i j hij,rfl⟩
  · obtain ⟨o,_,ho⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ho with he | he
    · exact Or.inr (Or.inr (Or.inr ⟨o,he⟩))
    · obtain ⟨e,_,he⟩ := List.mem_map.mp he
      cases he
      apply Or.inl
      have hedge : ∀ e : Fin 10, (XorGadget.arc e).1 ∈ xorPredecessors (XorGadget.arc e).2 := by decide
      exact List.mem_map.mpr ⟨(XorGadget.arc e).1,hedge e,rfl⟩

/-- Every assembled vertex has directed in-degree at most two. -/
theorem indegree_le_two {n m : Nat} (φ : Formula n m) (b : Vertex n m) :
    (Finset.univ.filter (fun a => Adj φ a b)).card ≤ 2 := by
  classical
  by_cases he : ∃ a, External φ a b
  · obtain ⟨a,ha⟩ := he
    have hsub : Finset.univ.filter (fun c => Adj φ c b) ⊆
        (internalPredecessors b).toFinset ∪ {a} := by
      intro c hc
      rcases incoming_internal_or_external φ (Finset.mem_filter.mp hc).2 with hc | hc
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hc)
      · exact Finset.mem_union_right _ (by simpa using external_source_unique φ hc ha)
    have hi := (List.toFinset_card_le (internalPredecessors b)).trans
      (internal_predecessor_length_of_external φ ha)
    calc
      _ ≤ ((internalPredecessors b).toFinset ∪ {a}).card := Finset.card_le_card hsub
      _ ≤ (internalPredecessors b).toFinset.card + 1 := by
        simpa using Finset.card_union_le (internalPredecessors b).toFinset {a}
      _ ≤ 2 := by omega
  · have hsub : Finset.univ.filter (fun c => Adj φ c b) ⊆ (internalPredecessors b).toFinset := by
      intro c hc
      rcases incoming_internal_or_external φ (Finset.mem_filter.mp hc).2 with hc | hc
      · exact List.mem_toFinset.mpr hc
      · exact False.elim (he ⟨c,hc⟩)
    exact (Finset.card_le_card hsub).trans
      ((List.toFinset_card_le _).trans (internal_predecessor_length_le_two b))

end GridHardness.PlanarSatAssembly
