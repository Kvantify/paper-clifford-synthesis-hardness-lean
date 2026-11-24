/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalPermutationCoreEdges

/-!
# Corrected SAT Interval Exterior Core Edges

The outer body links, obtained from the actual source slot list.
The final sweep edges hold for every height permutation. Nonempty and empty
variable/clause cases are stated separately, without supplied edge-membership
premises. No geometric routing is asserted here.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior
open PlanarSatAssembly CorrectedSatInterval.CoreEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

def first (hn : 0 <n) : Fin n := ⟨0,hn⟩
def last (hn : 0 <n) : Fin n := ⟨n-1,by omega⟩

@[simp] theorem first_val (hn : 0 <n) : (first hn).val=0 := rfl
@[simp] theorem last_val (hn : 0 <n) : (last hn).val=n-1 := rfl

theorem slot_sentinel (n m : Nat) :
    (slots n m)[0]'(by simp)= (sent 0,sent 2) := by
  simp [slots]

theorem slot_variable (v : Fin n) :
    (slots n m)[v.val+1]'(by simp; omega)=(var v false,var v true) := by
  simp only [slots]
  rw [List.getElem_append_left (by simp)]
  simp

theorem slot_clause (c : Fin m) :
    (slots n m)[n+c.val+1]'(by simp)=(clause c 8,clause c 1) := by
  simp only [slots]
  rw [List.getElem_append_right (by simp)]
  simp

/-- Consecutive positions in the actual slot list give a directed link. -/
theorem backbone_successive (i : Nat) (hi : i +1<(slots n m).length) :
    (((slots n m)[i]'(by omega)).2,
      ((slots n m)[i+1]'hi).1)∈backbone n m := by
  apply List.mem_iff_getElem.mpr
  refine ⟨i,?_,?_⟩
  · rw [slots_length] at hi
    rw [backbone_length]
    omega
  · simp only [backbone,List.getElem_zip,List.getElem_map]
    rw [List.getElem_append_left (by simp; rw [slots_length] at hi; omega)]
    simp only [List.getElem_tail,List.getElem_map]

/-- The last slot returns to the first sentinel, rather than to the first
variable or clause block. -/
theorem backbone_close :
    (((slots n m)[n+m]'(by simp)).2,sent 0)∈backbone n m := by
  apply List.mem_iff_getElem.mpr
  refine ⟨n+m,by simp,?_⟩
  simp only [backbone,List.getElem_zip,List.getElem_map]
  rw [List.getElem_append_right (by simp)]
  simp

theorem source_sentinel_variable (hn : 0 <n) :
    (sent (n:=n) (m:=m) 2,var (first hn) false)∈backbone n m := by
  have ht : (slots n m)[1]'(by simp; omega)=
      (var (first hn) false,var (first hn) true) := by
    simpa only [first_val,Nat.zero_add] using slot_variable (m:=m) (first hn)
  have h := backbone_successive (n:=n) (m:=m) 0 (by simp; omega)
  simpa only [slot_sentinel,Nat.zero_add,ht] using h

theorem source_variable_clause (hn : 0 <n) (hm : 0 <m) :
    (var (last hn) true,clause (first hm) 8)∈backbone n m := by
  have hs : (slots n m)[n]'(by simp)=
      (var (last hn) false,var (last hn) true) := by
    simpa only [last_val,show n-1+1=n by omega] using slot_variable (m:=m) (last hn)
  have ht : (slots n m)[n+1]'(by simp; omega)=
      (clause (first hm) 8,clause (first hm) 1) := by
    simpa only [first_val,Nat.add_zero] using slot_clause (n:=n) (first hm)
  have h := backbone_successive (n:=n) (m:=m) n (by simp; omega)
  simpa only [hs,ht] using h

theorem source_clause_sentinel (hm : 0 <m) :
    (clause (n:=n) (last hm) 1,sent 0)∈backbone n m := by
  have hs : (slots n m)[n+m]'(by simp)=
      (clause (last hm) 8,clause (last hm) 1) := by
    simpa only [last_val,show n+(m-1)+1=n+m by omega] using
      slot_clause (n:=n) (last hm)
  simpa only [hs] using (backbone_close (n:=n) (m:=m))

theorem source_variable_sentinel (hn : 0 <n) :
    (var (m:=0) (last hn) true,sent 0)∈backbone n 0 := by
  have hs : (slots n 0)[n]'(by simp)=
      (var (last hn) false,var (last hn) true) := by
    simpa only [last_val,show n-1+1=n by omega] using slot_variable (m:=0) (last hn)
  simpa only [Nat.add_zero,hs] using (backbone_close (n:=n) (m:=0))

theorem source_sentinel_close :
    (sent (n:=0) (m:=0) 2,sent 0)∈backbone 0 0 := by
  simpa only [Nat.zero_add,slot_sentinel] using (backbone_close (n:=0) (m:=0))

/-- This source edge is meaningful independently of whether a formula
with no variables and a nonempty clause list can exist. -/
theorem source_sentinel_clause (hm : 0 <m) :
    (sent (n:=0) (m:=m) 2,clause (first hm) 8)∈backbone 0 m := by
  have h := backbone_successive (n:=0) (m:=m) 0 (by simp; omega)
  have ht : (slots 0 m)[1]'(by simp; omega)=
      (clause (first hm) 8,clause (first hm) 1) := by
    simpa only [first_val,Nat.zero_add] using slot_clause (n:=0) (first hm)
  simpa only [slot_sentinel,Nat.zero_add,ht] using h

theorem backbone_edge (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (u v : PlanarSatAssembly.Vertex n m) (h : (u, v) ∈backbone n m) :
    (graph φ p).adj (liftOriginal φ p u) (liftOriginal φ p v) := by
  have hb := backbone_body u v h
  apply (body_adj φ p u v hb.1 hb.2).mpr
  simp only [Adj,edges,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem sentinel_first (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    (graph φ p).adj (liftOriginal φ p (sent 0)) (liftOriginal φ p (sent 1)) := by
  apply (body_adj φ p _ _ (sent_body 0) (sent_body 1)).mpr
  simp only [Adj,edges,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (by simp))))

theorem sentinel_second (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    (graph φ p).adj (liftOriginal φ p (sent 1)) (liftOriginal φ p (sent 2)) := by
  apply (body_adj φ p _ _ (sent_body 1) (sent_body 2)).mpr
  simp only [Adj,edges,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (by simp))))

theorem sentinel_variable (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (hn : 0 <n) :
    (graph φ p).adj (liftOriginal φ p (sent 2))
      (liftOriginal φ p (var (first hn) false)) :=
  backbone_edge φ p _ _ (source_sentinel_variable hn)

theorem variable_clause (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (hn : 0 <n) (hm : 0 <m) :
    (graph φ p).adj (liftOriginal φ p (var (last hn) true))
      (liftOriginal φ p (clause (first hm) 8)) :=
  backbone_edge φ p _ _ (source_variable_clause hn hm)

theorem clause_sentinel (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (hm : 0 <m) :
    (graph φ p).adj (liftOriginal φ p (clause (last hm) 1))
      (liftOriginal φ p (sent 0)) :=
  backbone_edge φ p _ _ (source_clause_sentinel hm)

theorem variable_sentinel (φ : Formula n 0) (p : Equiv.Perm (Fin (3 *0))) (hn : 0 <n) :
    (graph φ p).adj (liftOriginal φ p (var (last hn) true)) (liftOriginal φ p (sent 0)) :=
  backbone_edge φ p _ _ (source_variable_sentinel hn)

theorem sentinel_close (φ : Formula 0 0) (p : Equiv.Perm (Fin (3 *0))) :
    (graph φ p).adj (liftOriginal φ p (sent 2)) (liftOriginal φ p (sent 0)) :=
  backbone_edge φ p _ _ source_sentinel_close

end GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior
