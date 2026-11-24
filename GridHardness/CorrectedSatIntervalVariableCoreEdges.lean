/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalPermutationCoreEdges

/-!
# Corrected SAT Interval Variable Core Edges

The exact induced variable-vertex subgraph after any occurrence sweep.
It consists of the direct edge in each variable block and the backbone
edges between consecutive variables. Empty occurrence chains introduce
only another copy of the existing direct edge.
-/

public section

namespace GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges
open PlanarSatAssembly CorrectedSatInterval.CoreEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

private theorem variable_exit_get (v : Fin n) :
    ((slots n m).map Prod.snd)[v.val+1]'(by simp; omega)=var v true := by
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  rw [List.getElem_append_left (by simp)]
  simp

private theorem variable_entry_get (v : Fin n) :
    (((slots n m).map Prod.fst).tail ++ [sent 0])[v.val]'(by simp; omega)=
      var v false := by
  rw [List.getElem_append_left (by simp; omega)]
  simp only [List.getElem_tail,slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  rw [List.getElem_append_left (by simp)]
  simp

private theorem variable_entries_nodup (n m : Nat) :
    (((slots n m).map Prod.fst).tail ++ [sent 0]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(slots_entry_nodup n m).tail,by simp,?_⟩
  intro x hx y hy hxy
  have hy' : y=sent (n:=n) (m:=m) 0 := by simpa using hy
  have hx' : x=sent (n:=n) (m:=m) 0 := hxy.trans hy'
  rw [hx'] at hx
  simp [slots,sent,var,clause] at hx

theorem backbone_variable_iff (v w : Fin n) (a b : Bool) :
    (var (m:=m) v a,var w b)∈backbone n m ↔
      a=true ∧ b=false ∧ v.val+1=w.val := by
  constructor
  · intro h
    have hs := (List.of_mem_zip h).1
    have ht := (List.of_mem_zip h).2
    have ha : a=true := (by simpa [slots,var,sent,clause] using hs : true=a).symm
    have hb : b=false := by
      simp only [List.mem_append,List.mem_singleton] at ht
      rcases ht with ht | ht
      · exact (by simpa [slots,var,sent,clause] using List.mem_of_mem_tail ht : false=b).symm
      · simp [var,sent] at ht
    subst a
    subst b
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    simp only [backbone,List.getElem_zip] at he
    have hsource : i=v.val+1 := (slots_exit_nodup n m).getElem_inj_iff.mp
      ((congrArg Prod.fst he).trans (variable_exit_get (m:=m) v).symm)
    have htarget : i=w.val := (variable_entries_nodup n m).getElem_inj_iff.mp
      ((congrArg Prod.snd he).trans (variable_entry_get (m:=m) w).symm)
    exact ⟨rfl,rfl,by omega⟩
  · rintro ⟨rfl,rfl,hvw⟩
    have hi : v.val+1<(backbone n m).length := by simp; omega
    apply List.mem_iff_getElem.mpr
    refine ⟨v.val+1,hi,?_⟩
    simp only [backbone,List.getElem_zip]
    apply Prod.ext
    · exact variable_exit_get v
    · simpa only [hvw] using variable_entry_get (m:=m) w

/-- A chain edge with both endpoints in variable blocks can only duplicate
the direct entry-to-exit edge of its own block. -/
theorem variableChain_variable_endpoints (φ : Formula n m) (t v w : Fin n) (a b : Bool)
    (h : (var v a, var w b) ∈variableChain φ t) : v=w ∧ a=false ∧ b=true := by
  have hs := (List.of_mem_zip h).1
  have ht := (List.of_mem_zip h).2
  have hs' : v=t ∧ a=false := by simpa [var,PlanarSatAssembly.xor] using hs
  have ht' : w=t ∧ b=true := by simpa [var,PlanarSatAssembly.xor] using ht
  exact ⟨hs'.1.trans ht'.1.symm,hs'.2,ht'.2⟩

theorem source_variable_adj (φ : Formula n m) (v w : Fin n) (a b : Bool) :
    Adj φ (var v a) (var w b) ↔
      (v=w ∧ a=false ∧ b=true) ∨ (w.val=v.val+1 ∧ a=true ∧ b=false) := by
  constructor
  · intro h
    simp only [Adj,edges,List.mem_append] at h
    rcases h with (((hs | hb) | hv) | hc) | hx
    · simp [var,sent] at hs
    · have h := (backbone_variable_iff v w a b).mp hb
      exact Or.inr ⟨h.2.2.symm,h.1,h.2.1⟩
    · obtain ⟨t,_,hv⟩ := List.mem_flatMap.mp hv
      rcases List.mem_cons.mp hv with hv | hv
      · have hs := congrArg Prod.fst hv
        have ht := congrArg Prod.snd hv
        have hs' : v=t ∧ a=false := by simpa [var] using hs
        have ht' : w=t ∧ b=true := by simpa [var] using ht
        exact Or.inl ⟨hs'.1.trans ht'.1.symm,hs'.2,ht'.2⟩
      · exact Or.inl (variableChain_variable_endpoints φ t v w a b hv)
    · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨⟨u,z⟩,_,he⟩ := List.mem_map.mp hc
      have hs := congrArg Prod.fst he
      simp [clause,var] at hs
    · obtain ⟨o,_,ho⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp ho with ho | ho
      · simp [clauseLinks,clause,var,PlanarSatAssembly.xor] at ho
      · obtain ⟨e,_,he⟩ := List.mem_map.mp ho
        have hs := congrArg Prod.fst he
        simp [var,PlanarSatAssembly.xor] at hs
  · intro h
    simp only [Adj,edges,List.mem_append]
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨hvw,rfl,rfl⟩
    · exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr
        ⟨v,List.mem_finRange v,List.mem_cons_self⟩)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr
        ((backbone_variable_iff v w true false).mpr ⟨rfl,rfl,hvw.symm⟩))))

/-- Complete adjacency in the induced variable-vertex subgraph of the
actual graph for any height permutation. -/
theorem variable_adj_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v w : Fin n) (a b : Bool) :
    (graph φ p).adj (liftOriginal φ p (var v a)) (liftOriginal φ p (var w b)) ↔
      (v=w ∧ a=false ∧ b=true) ∨ (w.val=v.val+1 ∧ a=true ∧ b=false) :=
  (body_adj φ p _ _ (var_body v a) (var_body w b)).trans (source_variable_adj φ v w a b)

theorem variable_internal_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v : Fin n) (a b : Bool) :
    (graph φ p).adj (liftOriginal φ p (var v a)) (liftOriginal φ p (var v b)) ↔
      a=false ∧ b=true := by
  rw [variable_adj_iff]
  have hn : ¬v.val=v.val+1 := by omega
  simp only [true_and,hn,false_and,or_false]

theorem variable_backbone_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v w : Fin n) :
    (graph φ p).adj (liftOriginal φ p (var v true)) (liftOriginal φ p (var w false)) ↔
      w.val=v.val+1 := by
  rw [variable_adj_iff]
  simp

end GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges
