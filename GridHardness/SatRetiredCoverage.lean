/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRouteCatalogue
public import GridHardness.SatColumnCoverage
public import GridHardness.SatRowCoverage

/-!
# SAT Retired Coverage

Completeness of the route catalogue at the eight vertices of every
retired occurrence XOR. The total directed-degree bound rules out any
additional arc once the three catalogued incidences have been exhibited.
-/

@[expose] public section

namespace GridHardness.SatRetiredCoverage
open CliffordComplexity PlanarSatAssembly CorrectedSatInterval
open SatRouteCatalogue SatCrossingRetirement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def vertex (x : SatTy.denote) (j : Fin (3 *x.length)) (k : Fin 8) :
    SatRouteCatalogue.Vertex x :=
  PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inl (j,k))

theorem vertex_injective (x : SatTy.denote) (j : Fin (3 *x.length)) :
    Function.Injective (vertex x j) := by
  intro k l h
  exact (Prod.mk.inj (Sum.inl.inj
    (PermutationWirePlacement.vertex_injective _ _ h))).2

theorem side (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    Covers x (vertex x j (SatRetiredSideDrawing.localEndpoints e).1)
      (vertex x j (SatRetiredSideDrawing.localEndpoints e).2) :=
  covers_retired x (j,e)

theorem true_residual (x : SatTy.denote) (j : Fin (3 *x.length)) (r : Fin 4) :
    if r.val % 2 = 0 then ∃ u, Covers x u (vertex x j (trueVertex r))
    else ∃ u, Covers x (vertex x j (trueVertex r)) u := by
  classical
  by_cases he : Segments.EmptyColumn (permutation x) j
  · have h := covers_residual x ⟨j,r,.unsplit he⟩
    fin_cases r <;> dsimp [SatResidualDrawing.source,SatResidualDrawing.target,
      SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
      XorGadget.arc,XorLine.Marked.crossArc,trueVertex] at h ⊢ <;> exact ⟨_,h⟩
  · obtain ⟨⟨k,hk⟩,_⟩ := SatColumnCoverage.extrema (permutation x) j he
    have h := covers_residual x ⟨j,r,.below k hk⟩
    fin_cases r <;> dsimp [SatResidualDrawing.source,SatResidualDrawing.target,
      SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,trueVertex] at h ⊢ <;>
      try simp only [ite_true,ite_false,Nat.one_ne_zero] at h
    all_goals exact ⟨_,h⟩

theorem false_residual (x : SatTy.denote) (j : Fin (3 *x.length)) (r : Fin 4) :
    if r.val % 2 = 0 then ∃ u, Covers x (vertex x j (falseVertex r)) u
    else ∃ u, Covers x u (vertex x j (falseVertex r)) := by
  classical
  by_cases he : Segments.EmptyColumn (permutation x) j
  · have h := covers_residual x ⟨j,r,.unsplit he⟩
    fin_cases r <;> dsimp [SatResidualDrawing.source,SatResidualDrawing.target,
      SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
      XorGadget.arc,XorLine.Marked.crossArc,falseVertex] at h ⊢ <;> exact ⟨_,h⟩
  · obtain ⟨_,⟨k,hk⟩⟩ := SatColumnCoverage.extrema (permutation x) j he
    have h := covers_residual x ⟨j,r,.above k hk⟩
    fin_cases r <;> dsimp [SatResidualDrawing.source,SatResidualDrawing.target,
      SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,falseVertex] at h ⊢ <;>
      try simp only [ite_true,ite_false,Nat.one_ne_zero] at h
    all_goals exact ⟨_,h⟩

theorem vertex_original (x : SatTy.denote) (j : Fin (3 *x.length)) (k : Fin 8) :
    vertex x j k = PermutationGraph.liftOriginal (finiteFormula x) (permutation x)
      (PlanarSatAssembly.xor ((SatWireLayout.variableRank (finiteFormula x)).symm j) k) :=
  PermutationWirePlacement.vertex_original _ _ _ _

theorem chain_covers (x : SatTy.denote)
    (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    Covers x (SatVariableChainDrawing.vertex (finiteFormula x) (permutation x)
      (SatVariableChainDrawing.endpoints e).1)
      (SatVariableChainDrawing.vertex (finiteFormula x) (permutation x)
      (SatVariableChainDrawing.endpoints e).2) :=
  covers_outer x (.inl (.inr (.inl e)))

theorem chain_ne (x : SatTy.denote) (j : Fin (3 *x.length))
    (u : SatVariableChainDrawing.Vertex ((vsOf x).length +1) x.length)
    (k : Fin 8) (h0 : k ≠ 0) (h3 : k ≠ 3) :
    SatVariableChainDrawing.vertex (finiteFormula x) (permutation x) u ≠ vertex x j k := by
  rw [vertex_original]
  intro he
  have h := PermutationGraph.liftOriginal_injective (finiteFormula x) (permutation x) he
  rcases u with ⟨v,b⟩ | ⟨o,b⟩
  · cases h
  · have hk := congrArg (fun z : Occurrence x.length × Fin 8 => z.2)
      (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))
    cases b
    · exact h3 hk.symm
    · exact h0 hk.symm

theorem true_outgoing (x : SatTy.denote) (j : Fin (3 *x.length)) :
    ∃ u, Covers x (vertex x j 0) u ∧ u ≠ vertex x j 1 := by
  let φ := finiteFormula x
  let o := (SatWireLayout.variableRank φ).symm j
  let v := φ o.1 o.2
  obtain ⟨k,hk⟩ := SatVariableOrder.exists_indexedOccurrence φ v o
    ((mem_occurrencesOf φ v o).mpr rfl)
  have heq : SatVariableChainDrawing.vertex φ (permutation x) (.inr (o,true)) =
      vertex x j 0 := (vertex_original x j 0).symm
  by_cases hn : k.val+1 < SatVariableOrder.count φ v
  · let l : Fin (SatVariableOrder.count φ v) := ⟨k.val+1,hn⟩
    let e : SatVariableChainDrawing.Edge φ := .between v k l rfl
    have hc := chain_covers x e
    have hs : SatVariableChainDrawing.vertex φ (permutation x)
        (SatVariableChainDrawing.endpoints e).1 = vertex x j 0 := by
      change SatVariableChainDrawing.vertex φ (permutation x)
        (.inr (SatVariableOrder.indexedOccurrence φ v k,true)) = _
      rw [hk,heq]
    rw [hs] at hc
    exact ⟨_,hc,chain_ne x j _ 1 (by decide) (by decide)⟩
  · have hp : 0 < SatVariableOrder.count φ v := Nat.zero_lt_of_lt k.isLt
    let e : SatVariableChainDrawing.Edge φ := .exit v hp
    have hlast : (⟨SatVariableOrder.count φ v-1,by omega⟩ : Fin (SatVariableOrder.count φ v))=k :=
      Fin.ext (by dsimp; omega)
    have hc := chain_covers x e
    have hs : SatVariableChainDrawing.vertex φ (permutation x)
        (SatVariableChainDrawing.endpoints e).1 = vertex x j 0 := by
      change SatVariableChainDrawing.vertex φ (permutation x)
        (.inr (SatVariableOrder.indexedOccurrence φ v ⟨SatVariableOrder.count φ v-1,by omega⟩,true)) = _
      rw [hlast,hk,heq]
    rw [hs] at hc
    exact ⟨_,hc,chain_ne x j _ 1 (by decide) (by decide)⟩

theorem true_incoming (x : SatTy.denote) (j : Fin (3 *x.length)) :
    ∃ u, Covers x u (vertex x j 3) ∧ u ≠ vertex x j 2 := by
  let φ := finiteFormula x
  let o := (SatWireLayout.variableRank φ).symm j
  let v := φ o.1 o.2
  obtain ⟨k,hk⟩ := SatVariableOrder.exists_indexedOccurrence φ v o
    ((mem_occurrencesOf φ v o).mpr rfl)
  have heq : SatVariableChainDrawing.vertex φ (permutation x) (.inr (o,false)) =
      vertex x j 3 := (vertex_original x j 3).symm
  by_cases hz : k.val=0
  · have hp : 0 < SatVariableOrder.count φ v := Nat.zero_lt_of_lt k.isLt
    let e : SatVariableChainDrawing.Edge φ := .entry v hp
    have hfirst : (⟨0,hp⟩ : Fin (SatVariableOrder.count φ v))=k := Fin.ext hz.symm
    have hc := chain_covers x e
    have ht : SatVariableChainDrawing.vertex φ (permutation x)
        (SatVariableChainDrawing.endpoints e).2 = vertex x j 3 := by
      change SatVariableChainDrawing.vertex φ (permutation x)
        (.inr (SatVariableOrder.indexedOccurrence φ v ⟨0,hp⟩,false)) = _
      rw [hfirst,hk,heq]
    rw [ht] at hc
    exact ⟨_,hc,chain_ne x j _ 2 (by decide) (by decide)⟩
  · let l : Fin (SatVariableOrder.count φ v) := ⟨k.val-1,by omega⟩
    have hlk : k.val=l.val+1 := by dsimp [l]; omega
    let e : SatVariableChainDrawing.Edge φ := .between v l k hlk
    have hc := chain_covers x e
    have ht : SatVariableChainDrawing.vertex φ (permutation x)
        (SatVariableChainDrawing.endpoints e).2 = vertex x j 3 := by
      change SatVariableChainDrawing.vertex φ (permutation x)
        (.inr (SatVariableOrder.indexedOccurrence φ v k,false)) = _
      rw [hk,heq]
    rw [ht] at hc
    exact ⟨_,hc,chain_ne x j _ 2 (by decide) (by decide)⟩

theorem retained_ne (x : SatTy.denote) (j : Fin (3 *x.length))
    (c : WireCrossingSchedule.Cell (permutation x))
    (v : SatCrossingHorizontal.RetainedVertex) (k : Fin 8) :
    PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inr (c,v)) ≠
      vertex x j k := by
  intro h
  have he := PermutationWirePlacement.vertex_injective _ _ h
  cases he

theorem clause_ne (x : SatTy.denote) (j : Fin (3 *x.length))
    (o : Occurrence x.length) (b : Bool) (k : Fin 8) :
    SatClauseWireDrawing.clauseVertex (finiteFormula x) o b ≠ vertex x j k := by
  rw [vertex_original]
  intro h
  have he := PermutationGraph.liftOriginal_injective (finiteFormula x) (permutation x) h
  cases he

theorem false_external (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    ∃ u, (if b then Covers x (vertex x j 7) u else Covers x u (vertex x j 4)) ∧
      u ≠ vertex x j (if b then 6 else 5) := by
  cases hl : Catalogue.lastRequest? (permutation x) j with
  | none =>
    let o := (SatWireLayout.variableRank (finiteFormula x)).symm j
    have hrank : SatWireLayout.variableRank (finiteFormula x) o = j :=
      Equiv.apply_symm_apply _ _
    have hf := (SatRowCoverage.first_none_iff_last_none (permutation x) j).mpr hl
    have he : SatClauseWireDrawing.actualWireVertex (finiteFormula x) o b =
        vertex x j (if b then 7 else 4) := by
      unfold SatClauseWireDrawing.actualWireVertex
      rw [hrank,SatClauseWireDrawing.wireVertex_none _ _ b hf]
      rfl
    have hc := covers_outer x (.inr (o,b))
    change Covers x (SatClauseWireDrawing.source (finiteFormula x) o b)
      (SatClauseWireDrawing.target (finiteFormula x) o b) at hc
    simp only [SatClauseWireDrawing.source,SatClauseWireDrawing.target,he] at hc
    cases b <;> simp only [Bool.false_eq_true,ite_true,ite_false] at hc ⊢
    · exact ⟨_,hc,clause_ne x j o false 5⟩
    · exact ⟨_,hc,clause_ne x j o true 6⟩
  | some i =>
    let e : SatLastLinkDrawing.Edge (permutation x) := (⟨(i,j),hl⟩,b)
    have hc := covers_last x e
    cases b <;> dsimp [e,SatLastLinkDrawing.source,SatLastLinkDrawing.target,
      SatLastLinkDrawing.sourceWire,SatLastLinkDrawing.targetWire] at hc ⊢
    · exact ⟨_,hc,retained_ne x j _ _ 5⟩
    · exact ⟨_,hc,retained_ne x j _ _ 6⟩

theorem complete_in_two (x : SatTy.denote) (v a b c : SatRouteCatalogue.Vertex x)
    (hab : a ≠ b) (ha : Covers x a v) (hb : Covers x b v) (hc : Covers x v c) :
    LocalComplete x v := by
  apply complete_of_three x v ![.inl a,.inl b,.inr c]
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc

theorem complete_out_two (x : SatTy.denote) (v a b c : SatRouteCatalogue.Vertex x)
    (hbc : b ≠ c) (ha : Covers x a v) (hb : Covers x v b) (hc : Covers x v c) :
    LocalComplete x v := by
  apply complete_of_three x v ![.inl a,.inr b,.inr c]
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc

/-- Every incoming and outgoing arc at every retired occurrence-XOR
vertex belongs to the simultaneous route catalogue. -/
theorem local_complete (x : SatTy.denote) (j : Fin (3 *x.length)) (k : Fin 8) :
    LocalComplete x (vertex x j k) := by
  have hne (a b : Fin 8) (hab : a ≠ b) : vertex x j a ≠ vertex x j b :=
    fun h => hab (vertex_injective x j h)
  fin_cases k
  · obtain ⟨r,hr⟩ := true_residual x j 0
    obtain ⟨e,he,hne'⟩ := true_outgoing x j
    exact complete_out_two x _ r _ e hne'.symm hr (side x j 0) he
  · obtain ⟨r,hr⟩ := true_residual x j 1
    exact complete_in_two x _ _ _ r (hne 0 2 (by decide)) (side x j 0) (side x j 1) hr
  · obtain ⟨r,hr⟩ := true_residual x j 2
    exact complete_out_two x _ r _ _ (hne 1 3 (by decide)) hr (side x j 1) (side x j 2)
  · obtain ⟨r,hr⟩ := true_residual x j 3
    obtain ⟨e,he,hne'⟩ := true_incoming x j
    exact complete_in_two x _ _ e r hne'.symm (side x j 2) he hr
  · obtain ⟨r,hr⟩ := false_residual x j 0
    obtain ⟨e,he,hne'⟩ := false_external x j false
    exact complete_in_two x _ _ e r hne'.symm (side x j 3) he hr
  · obtain ⟨r,hr⟩ := false_residual x j 1
    exact complete_out_two x _ r _ _ (hne 4 6 (by decide)) hr (side x j 3) (side x j 4)
  · obtain ⟨r,hr⟩ := false_residual x j 2
    exact complete_in_two x _ _ _ r (hne 5 7 (by decide)) (side x j 4) (side x j 5) hr
  · obtain ⟨r,hr⟩ := false_residual x j 3
    obtain ⟨e,he,hne'⟩ := false_external x j true
    exact complete_out_two x _ r _ e hne'.symm hr (side x j 5) he

end GridHardness.SatRetiredCoverage
