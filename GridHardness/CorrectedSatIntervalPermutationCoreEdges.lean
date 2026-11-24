/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalCoreEdges
public import GridHardness.CorrectedSatIntervalPermutationGraph
public import GridHardness.PlanarSatDegree

/-!
# Corrected SAT Interval Permutation Core Edges

Exact original-body adjacency for every occurrence-height permutation.
The clause-to-clause backbone condition is derived from the source slot
list, including its end cases.
-/

public section

namespace GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges
open PlanarSatAssembly
open CorrectedSatInterval.CoreEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

theorem body_adj (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (u v : PlanarSatAssembly.Vertex n m) (hu : Body u) (hv : Body v) :
    (graph φ p).adj (liftOriginal φ p u) (liftOriginal φ p v) ↔ Adj φ u v :=
  body_run_adj φ (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (initial_ready φ p) u v hu hv

theorem clause_adj (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (c d : Fin m) (u v : Fin 12) :
    (graph φ p).adj (liftOriginal φ p (clause c u)) (liftOriginal φ p (clause d v)) ↔
      Adj φ (clause c u) (clause d v) :=
  body_adj φ p _ _ (clause_body c u) (clause_body d v)

private theorem exit_get (c : Fin m) :
    ((slots n m).map Prod.snd)[n+c.val+1]'(by simp <;> omega) = clause c 1 := by
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  rw [List.getElem_append_right (by simp <;> omega)]
  simp

private theorem entry_get (c : Fin m) :
    (((slots n m).map Prod.fst).tail ++ [sent 0])[n+c.val]'(by simp <;> omega) =
      clause c 8 := by
  rw [List.getElem_append_left (by simp <;> omega)]
  simp only [List.getElem_tail,slots,List.map_append,List.map_cons,List.map_nil,List.map_map]
  rw [List.getElem_append_right (by simp <;> omega)]
  simp

private theorem entries_nodup (n m : Nat) :
    (((slots n m).map Prod.fst).tail ++ [sent 0]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(slots_entry_nodup n m).tail,by simp,?_⟩
  intro x hx y hy hxy
  have hy' : y = sent (n := n) (m := m) 0 := by simpa using hy
  have hxs : x = sent (n := n) (m := m) 0 := hxy.trans hy'
  rw [hxs] at hx
  simp [slots,sent,var,clause] at hx

/-- The source construction joins clause `c` to clause `d` precisely when
`d` follows `c` in the original clause order. In particular the last clause
does not wrap around to the first clause. -/
theorem backbone_clause_iff (c d : Fin m) (u v : Fin 12) :
    (clause (n := n) c u,clause d v)∈backbone n m ↔
      u=1 ∧ v=8 ∧ c.val+1=d.val := by
  constructor
  · intro h
    have hs := (List.of_mem_zip h).1
    have ht := (List.of_mem_zip h).2
    have hu : u=1 := (by simpa [slots,clause,sent,var] using hs : 1=u).symm
    have hv : v=8 := by
      simp only [List.mem_append,List.mem_singleton] at ht
      rcases ht with ht | ht
      · exact (by simpa [slots,clause,sent,var] using List.mem_of_mem_tail ht : 8=v).symm
      · simp [clause,sent] at ht
    subst u
    subst v
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    simp only [backbone,List.getElem_zip] at he
    have hsource : i=n+c.val+1 := (slots_exit_nodup n m).getElem_inj_iff.mp
      ((congrArg Prod.fst he).trans (exit_get (n := n) c).symm)
    have htarget : i=n+d.val := (entries_nodup n m).getElem_inj_iff.mp
      ((congrArg Prod.snd he).trans (entry_get (n := n) d).symm)
    exact ⟨rfl,rfl,by omega⟩
  · rintro ⟨rfl,rfl,hcd⟩
    have hi : n+c.val+1 < (backbone n m).length := by simp <;> omega
    apply List.mem_iff_getElem.mpr
    refine ⟨n+c.val+1,hi,?_⟩
    simp only [backbone,List.getElem_zip]
    apply Prod.ext
    · exact exit_get c
    · have he : n+c.val+1=n+d.val := by omega
      simpa only [he] using entry_get (n := n) d

theorem source_clause_adj (φ : Formula n m) (c d : Fin m) (u v : Fin 12) :
    Adj φ (clause c u) (clause d v) ↔
      (c=d ∧ (u,v)∈clauseBody) ∨ (d.val=c.val+1 ∧ u=1 ∧ v=8) := by
  constructor
  · intro h
    simp only [Adj,edges,List.mem_append] at h
    rcases h with (((hs | hb) | hv) | hc) | hx
    · simp [clause,sent] at hs
    · have h := (backbone_clause_iff c d u v).mp hb
      exact Or.inr ⟨h.2.2.symm,h.1,h.2.1⟩
    · obtain ⟨w,_,hv⟩ := List.mem_flatMap.mp hv
      rcases List.mem_cons.mp hv with hv | hv
      · simp [clause,var] at hv
      · have hm := (List.of_mem_zip hv).1
        simp [clause,var,PlanarSatAssembly.xor] at hm
    · obtain ⟨e,_,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hc
      have hs := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      simp only [clause,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at hs ht
      rcases hs with ⟨rfl,rfl⟩
      rcases ht with ⟨rfl,rfl⟩
      exact Or.inl ⟨rfl,hab⟩
    · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp ha with ha | ha
      · simp [clauseLinks,clause,PlanarSatAssembly.xor] at ha
      · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
        have hs := congrArg Prod.fst he
        simp [clause,PlanarSatAssembly.xor] at hs
  · intro h
    simp only [Adj,edges,List.mem_append]
    rcases h with ⟨rfl,h⟩ | ⟨hcd,rfl,rfl⟩
    · exact Or.inl (Or.inr (List.mem_flatMap.mpr
        ⟨c,List.mem_finRange c,List.mem_map.mpr ⟨(u,v),h,rfl⟩⟩))
    · exact Or.inl (Or.inl (Or.inl (Or.inr
        ((backbone_clause_iff c d 1 8).mpr ⟨rfl,rfl,hcd.symm⟩))))

/-- Complete adjacency of the induced clause-vertex subgraph after any
permutation sweep, expressed in the original clause vertex names. -/
theorem clause_adj_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (c d : Fin m) (u v : Fin 12) :
    (graph φ p).adj (liftOriginal φ p (clause c u)) (liftOriginal φ p (clause d v)) ↔
      (c=d ∧ (u,v)∈clauseBody) ∨ (d.val=c.val+1 ∧ u=1 ∧ v=8) :=
  (clause_adj φ p c d u v).trans (source_clause_adj φ c d u v)

theorem clause_internal_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (c : Fin m) (u v : Fin 12) :
    (graph φ p).adj (liftOriginal φ p (clause c u)) (liftOriginal φ p (clause c v)) ↔
      (u,v)∈clauseBody := by
  rw [clause_adj_iff]
  have hn : ¬c.val=c.val+1 := by omega
  simp only [true_and,hn,false_and,or_false]

theorem clause_backbone_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (c d : Fin m) :
    (graph φ p).adj (liftOriginal φ p (clause c 1)) (liftOriginal φ p (clause d 8)) ↔
      d.val=c.val+1 := by
  rw [clause_adj_iff]
  have hn : ((1,8) : Fin 12 × Fin 12)∉clauseBody := by decide
  simp only [hn,and_false,false_or,and_self,and_true]

end GridHardness.CorrectedSatInterval.PermutationGraph.CoreEdges
