/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRouteCatalogue

/-!
# SAT Body Coverage

Exhaustiveness of the body route catalogue. Every arc between two
original sentinel, variable or clause vertices occurs among the body or
exterior routes; this includes empty variable chains and the empty formula.
-/

public section

namespace GridHardness.SatBodyCoverage
open CliffordComplexity PlanarSatAssembly CorrectedSatInterval
open PermutationGraph.CoreEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev lift (x : SatTy.denote) :=
  PermutationGraph.liftOriginal (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x))

abbrev Covered (x : SatTy.denote)
    (u v : PlanarSatAssembly.Vertex ((vsOf x).length +1) x.length) : Prop :=
  ∃ e : SatBodyChainDrawing.Edge x,
    SatBodyChainDrawing.source x e = lift x u ∧
    SatBodyChainDrawing.target x e = lift x v

private theorem backbone_get {n m : Nat} (i : Nat) (hi : i +1<(slots n m).length) :
    (backbone n m)[i]'(by simp at hi ⊢; omega) =
      (((slots n m)[i]'(by omega)).2,((slots n m)[i+1]'hi).1) := by
  simp only [backbone,List.getElem_zip,List.getElem_map]
  rw [List.getElem_append_left (by simp; rw [slots_length] at hi; omega)]
  simp only [List.getElem_tail,List.getElem_map]

private theorem backbone_get_last {n m : Nat} :
    (backbone n m)[n+m]'(by simp) = (((slots n m)[n+m]'(by simp)).2,sent 0) := by
  simp only [backbone,List.getElem_zip,List.getElem_map]
  rw [List.getElem_append_right (by simp)]
  simp

private theorem successive_covered (x : SatTy.denote) (i : Nat)
    (hi : i +1<(slots ((vsOf x).length +1) x.length).length) :
    Covered x ((slots ((vsOf x).length+1) x.length)[i]'(by omega)).2
      ((slots ((vsOf x).length+1) x.length)[i+1]'hi).1 := by
  have hib : i < (vsOf x).length+1+x.length := by simpa using hi
  by_cases hiz : i=0
  · subst i
    rw [Exterior.slot_sentinel]
    have ht := Exterior.slot_variable (m:=x.length) (SatExteriorDrawing.firstVar x)
    have hi1 : (SatExteriorDrawing.firstVar x).val+1=1 := rfl
    simp only [hi1] at ht
    rw [ht]
    exact ⟨.inr (.inr .firstVariable),rfl,rfl⟩
  · by_cases hiv : i<(vsOf x).length+1
    · let v : Fin ((vsOf x).length+1) := ⟨i-1,by omega⟩
      let w : Fin ((vsOf x).length+1) := ⟨i,hiv⟩
      have hs := Exterior.slot_variable (m:=x.length) v
      have ht := Exterior.slot_variable (m:=x.length) w
      have hv : v.val+1=i := by dsimp [v]; omega
      simp only [hv] at hs
      rw [hs,ht]
      exact ⟨.inl (.inl (.backbone v w (by dsimp [v,w]; omega))),rfl,rfl⟩
    · by_cases hie : i=(vsOf x).length+1
      · subst i
        have hm : 0<x.length := by omega
        have hs := Exterior.slot_variable (m:=x.length) (SatExteriorDrawing.lastVar x)
        have ht := Exterior.slot_clause (n:=(vsOf x).length+1) (Exterior.first hm)
        have hv : (SatExteriorDrawing.lastVar x).val+1=(vsOf x).length+1 := by
          simp [SatExteriorDrawing.lastVar,Exterior.last]
        simp only [hv] at hs
        simp only [Exterior.first_val,Nat.add_zero] at ht
        rw [hs,ht]
        exact ⟨.inr (.inr (.forward hm)),rfl,rfl⟩
      · let c : Fin x.length := ⟨i-((vsOf x).length+1)-1,by omega⟩
        let d : Fin x.length := ⟨i-((vsOf x).length+1),by omega⟩
        have hs := Exterior.slot_clause (n:=(vsOf x).length+1) c
        have ht := Exterior.slot_clause (n:=(vsOf x).length+1) d
        have hc : (vsOf x).length+1+c.val+1=i := by dsimp [c]; omega
        have hd : (vsOf x).length+1+d.val+1=i+1 := by dsimp [d]; omega
        simp only [hc] at hs
        simp only [hd] at ht
        rw [hs,ht]
        exact ⟨.inl (.inr (.backbone c d (by dsimp [c,d]; omega))),rfl,rfl⟩

private theorem closing_covered (x : SatTy.denote) :
    Covered x ((slots ((vsOf x).length+1) x.length)[(vsOf x).length+1+x.length]'(by simp)).2 (sent 0) := by
  by_cases hm : 0<x.length
  · have hs := Exterior.slot_clause (n:=(vsOf x).length+1) (Exterior.last hm)
    have hc : (vsOf x).length+1+(Exterior.last hm).val+1=
        (vsOf x).length+1+x.length := by simp only [Exterior.last_val]; omega
    simp only [hc] at hs
    rw [hs]
    exact ⟨.inr (.inr (.returning hm)),rfl,rfl⟩
  · have hz : x.length=0 := by omega
    have hs := Exterior.slot_variable (m:=x.length) (SatExteriorDrawing.lastVar x)
    have hv : (SatExteriorDrawing.lastVar x).val+1=(vsOf x).length+1+x.length := by
      simp [SatExteriorDrawing.lastVar,Exterior.last,hz]
    simp only [hv] at hs
    rw [hs]
    exact ⟨.inr (.inr (.closing hz)),rfl,rfl⟩

/-- All source backbone arcs, including the wrap to the first sentinel,
have explicit routes in the assembled catalogue. -/
theorem backbone_covered (x : SatTy.denote)
    (u v : PlanarSatAssembly.Vertex ((vsOf x).length +1) x.length)
    (h : (u, v) ∈backbone ((vsOf x).length +1) x.length) : Covered x u v := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
  by_cases hil : i<(vsOf x).length+1+x.length
  · have his : i+1<(slots ((vsOf x).length+1) x.length).length := by simp; omega
    rw [backbone_get i his] at he
    have hu := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    dsimp only at hu hv
    rw [← hu,← hv]
    exact successive_covered x i his
  · have hie : i=(vsOf x).length+1+x.length := by simp only [backbone_length] at hi; omega
    subst i
    rw [backbone_get_last] at he
    have hu := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    dsimp only at hu hv
    rw [← hu,← hv]
    exact closing_covered x

/-- Original-body arcs cannot arise from clause-wire or XOR-internal arcs.
An empty variable chain can only duplicate its direct body arc. -/
theorem source_covered (x : SatTy.denote)
    (u v : PlanarSatAssembly.Vertex ((vsOf x).length +1) x.length)
    (hu : CoreEdges.Body u) (hv : CoreEdges.Body v)
    (h : Adj (finiteFormula x) u v) : Covered x u v := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hw) | hc) | hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with he | he
    · cases he
      exact ⟨.inr (.inr .sentinelFirst),rfl,rfl⟩
    · cases he
      exact ⟨.inr (.inr .sentinelSecond),rfl,rfl⟩
  · exact backbone_covered x u v hb
  · obtain ⟨w,_,hw⟩ := List.mem_flatMap.mp hw
    rcases List.mem_cons.mp hw with he | he
    · cases he
      exact ⟨.inl (.inl (.direct w)),rfl,rfl⟩
    · have hs := (List.of_mem_zip he).1
      have ht := (List.of_mem_zip he).2
      simp only [List.mem_cons,List.mem_map] at hs
      rcases hs with hs | ⟨o,_,ho⟩
      · subst u
        simp only [List.mem_append,List.mem_map,List.mem_singleton] at ht
        rcases ht with ⟨o,_,ho⟩ | ht
        · exact False.elim (hv o 3 ho)
        · subst v
          exact ⟨.inl (.inl (.direct w)),rfl,rfl⟩
      · exact False.elim (hu o 0 ho)
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨⟨a,b⟩,hab,he⟩ := List.mem_map.mp hc
    obtain ⟨e,he'⟩ := (PlanarSatClause.Lattice.body_iff_edge a b).mp hab
    cases he
    refine ⟨.inl (.inr (.internal c e)),?_,?_⟩
    · change lift x (clause c (PlanarSatClause.Lattice.edge e).1) = lift x (clause c a)
      rw [he']
    · change lift x (clause c (PlanarSatClause.Lattice.edge e).2) = lift x (clause c b)
      rw [he']
  · obtain ⟨o,_,hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [clauseLinks,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with he | he
      · exact False.elim (hv o 4 (congrArg Prod.snd he).symm)
      · exact False.elim (hu o 7 (congrArg Prod.fst he).symm)
    · obtain ⟨e,_,he⟩ := List.mem_map.mp hx
      exact False.elim (hu o (XorGadget.arc e).1 (congrArg Prod.fst he))

/-- Every final-graph arc with two original body endpoints is in the
simultaneous route catalogue. No formula-width or drawing premise is needed. -/
theorem body_covered (x : SatTy.denote)
    (u v : PermutationWirePlacement.BodyVertex ((vsOf x).length +1) x.length)
    (h : (SatClauseOrder.graph (finiteFormula x)).adj
      (PermutationWirePlacement.bodyVertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) u)
      (PermutationWirePlacement.bodyVertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) v)) :
    SatRouteCatalogue.Covers x
      (PermutationWirePlacement.bodyVertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) u)
      (PermutationWirePlacement.bodyVertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) v) := by
  have hu : CoreEdges.Body (PermutationWirePlacement.bodyNames u) :=
    fun o k => (PermutationWirePlacement.bodyNames_ne_xor u o k).symm
  have hv : CoreEdges.Body (PermutationWirePlacement.bodyNames v) :=
    fun o k => (PermutationWirePlacement.bodyNames_ne_xor v o k).symm
  have hs := (body_adj (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x))
    _ _ hu hv).mp h
  obtain ⟨e,he,ht⟩ := source_covered x _ _ hu hv hs
  have hc := SatRouteCatalogue.covers_outer x (.inl e)
  change SatRouteCatalogue.Covers x (SatBodyChainDrawing.source x e)
    (SatBodyChainDrawing.target x e) at hc
  rw [he,ht] at hc
  exact hc

end GridHardness.SatBodyCoverage
