/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCodeAssembly

/-!
# Planar SAT Code

Relate the computed vertex and edge lists to the variable chains, clause gadgets,
and occurrence edges of the SAT graph.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.PlanarSatCode
open CliffordComplexity PlanarSatAssembly

attribute [local irreducible] variableChainCode backboneCode

theorem mem_variableEdgesAt (x : SatTy.denote) (v : Fin ((vsOf x).length +1))
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ variableEdgesAt.eval (x,v.val) ↔
      (a,b) ∈ (var v false,var v true) :: variableChain (finiteFormula x) v := by
  rw [variableEdgesAt]
  change _ ∈ ((varNum false).eval v.val, (varNum true).eval v.val) ::
    variableChainCode.eval (x,v.val) ↔ _
  simp only [List.mem_cons, varNum_eval]
  refine or_congr ?_ (mem_variableChainCode x v a b)
  constructor
  · intro h
    apply (numbering ((vsOf x).length+1) x.length).num_pair_inj
    simpa only [numbering_var] using h
  · intro h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    simp only [numbering_var]

theorem mem_variableEdgesCode (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ variableEdgesCode.eval x ↔
      (a,b) ∈ (List.finRange ((vsOf x).length+1)).flatMap
        (fun v => (var v false,var v true) :: variableChain (finiteFormula x) v) := by
  change _ ∈ ((variableIndices.eval x).map (fun v => variableEdgesAt.eval (x,v))).flatten ↔ _
  rw [variableIndices_finite]
  simp only [List.map_map,Function.comp_def,← List.flatMap_def,List.mem_flatMap]
  exact exists_congr (fun v => and_congr_right (fun _ => mem_variableEdgesAt x v a b))

theorem mem_clauseEdgesCode (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ clauseEdgesCode.eval x ↔
      (a,b) ∈ (List.finRange x.length).flatMap clauseEdges := by
  change _ ∈ ((clauses.eval x).map (fun c => clauseEdgesAt.eval (x,c))).flatten ↔ _
  rw [clauses_finite]
  simp only [List.map_map,Function.comp_def,← List.flatMap_def,List.mem_flatMap]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  rw [clauseEdgesAt_eval]
  exact (numbering _ _).mem_map_num_pair

theorem mem_occurrenceEdgesCode (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ occurrenceEdgesCode.eval x ↔
      (a,b) ∈ (occurrences x.length).flatMap (fun o => clauseLinks o ++ xorEdges o) := by
  change _ ∈ ((occurrencesCode.eval x).map (fun o => occurrenceEdgesAt.eval (x,o))).flatten ↔ _
  rw [occurrencesCode_eval]
  simp only [List.map_map,Function.comp_def,← List.flatMap_def,List.mem_flatMap]
  apply exists_congr
  intro o
  apply and_congr_right
  intro _
  rw [occurrenceEdgesAt_eval]
  exact (numbering _ _).mem_map_num_pair

/-- Every emitted arc is exactly an arc of the proved finite SAT assembly. -/
theorem mem_edgesCode (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ edgesCode.eval x ↔
      Adj (finiteFormula x) a b := by
  have hsent : ((numbering _ _).num a,(numbering _ _).num b) ∈ [(0,1),(1,2)] ↔
      (a,b) ∈ [(sent 0,sent 1),(sent 1,sent 2)] :=
    (numbering ((vsOf x).length+1) x.length).mem_map_num_pair
      (L := [(sent 0,sent 1),(sent 1,sent 2)]) (u := a) (w := b)
  rw [edgesCode, append_eval, append_eval, append_eval, append_eval]
  simp only [Code.eval, Adj, edges, List.mem_append]
  exact or_congr (or_congr (or_congr (or_congr hsent (mem_backboneCode x a b))
    (mem_variableEdgesCode x a b)) (mem_clauseEdgesCode x a b)) (mem_occurrenceEdgesCode x a b)

/-- Position decoding is bijective and preserves all directed arcs. -/
noncomputable def decodeEquiv (x : SatTy.denote) :
    Vertex ((vsOf x).length+1) x.length ≃ Fin (assembly.eval x).1.length :=
  (numbering ((vsOf x).length+1) x.length).equivFin.trans
    (finCongr (verticesCode_length x).symm)

@[simp] theorem decodeEquiv_val (x : SatTy.denote)
    (a : Vertex ((vsOf x).length +1) x.length) :
    (decodeEquiv x a).val = (numbering _ _).num a := rfl

theorem assembly_arc_iff (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((decodeEquiv x a).val,(decodeEquiv x b).val) ∈ (assembly.eval x).2.1 ↔
      Adj (finiteFormula x) a b := by
  have h : (assembly.eval x).2.1 = edgesCode.eval x := rfl
  rw [decodeEquiv_val, decodeEquiv_val, h]
  exact mem_edgesCode x a b

theorem assembly_correct (x : SatTy.denote) :
    PlanarSatReduction.Hamiltonian (finiteFormula x) ↔
      DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE (assembly.eval x) := by
  have hn : 0 < (assembly.eval x).1.length := by
    change 0 < (verticesCode.eval x).length
    rw [verticesCode_length,numbering_size]
    omega
  let e := decodeEquiv x
  constructor
  · rintro ⟨next,ho,ha⟩
    refine ⟨hn,e.symm.trans (next.trans e),?_,?_⟩
    · exact ho.transport e (by intro v; simp)
    · intro w
      obtain ⟨v,rfl⟩ := e.surjective w
      simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using
        (assembly_arc_iff x v (next v)).mpr (ha v)
  · rintro ⟨_,next,ho,ha⟩
    refine ⟨e.trans (next.trans e.symm),?_,?_⟩
    · exact ho.transport e.symm (by intro v; simp)
    · intro v
      apply (assembly_arc_iff x v _).mp
      simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply] using ha (e v)

/-- A bounded list scan checks the concrete positive three-literal syntax. -/
def allCode : Code (.list .bool) .bool := Code.isNil (.listFilter .boolNot)

def clauseSyntax : Code (.list (.pair .nat .bool)) .bool :=
  .comp (.pair (.comp (.pair .listLen (.const .nat 3)) .natEq)
    (.comp (.listMap .snd) allCode)) .boolAnd

def syntaxGuard : Code SatTy .bool := .comp (.listMap clauseSyntax) allCode

def code : Code SatTy GraphTy := .branch syntaxGuard assembly (.const GraphTy ([],([],0)))

theorem allCode_eval (l : List Bool) : allCode.eval l = true ↔ ∀ b ∈ l, b = true := by
  rw [allCode,isNil_eval_true]
  change l.filter Bool.not = [] ↔ _
  simp

theorem clauseSyntax_eval (c : List (Nat ×Bool)) : clauseSyntax.eval c = true ↔
    c.length = 3 ∧ ∀ p ∈ c, p.2 = true := by
  change (decide (c.length = 3) && allCode.eval (c.map Prod.snd)) = true ↔ _
  rw [Bool.and_eq_true,decide_eq_true_eq,allCode_eval]
  simp only [List.forall_mem_map]

theorem syntaxGuard_eval (x : SatTy.denote) : syntaxGuard.eval x = true ↔
    (∀ c ∈ x, c.length = 3) ∧ (∀ c ∈ x, ∀ p ∈ c, p.2 = true) := by
  change allCode.eval (x.map clauseSyntax.eval) = true ↔ _
  rw [allCode_eval]
  simp only [List.forall_mem_map]
  constructor
  · intro h
    exact ⟨fun c hc => ((clauseSyntax_eval c).mp (h c hc)).1,
      fun c hc => ((clauseSyntax_eval c).mp (h c hc)).2⟩
  · rintro ⟨hw,hp⟩ c hc
    exact (clauseSyntax_eval c).mpr ⟨hw c hc,hp c hc⟩

/-- Malformed syntax is sent to the empty directed graph, a no-instance. -/
theorem code_correct (x : SatTy.denote) : Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE (code.eval x) := by
  by_cases h : syntaxGuard.eval x = true
  · rw [code,branch_eval_true _ _ h]
    obtain ⟨hw,hp⟩ := (syntaxGuard_eval x).mp h
    exact (PlanarSatReduction.positiveSat_correct x hw hp).trans (assembly_correct x)
  · have hs : ¬ Concrete.MONOTONE_ONE_IN_THREE_SAT3 x := by
      intro hx
      obtain ⟨hp,hw,_⟩ := (Concrete.monotoneOneInThree3Sat_iff x).mp hx
      exact h ((syntaxGuard_eval x).mpr ⟨hw,hp⟩)
    have hf : syntaxGuard.eval x = false := Bool.eq_false_iff.mpr h
    rw [code,branch_eval_false _ _ hf]
    simp [hs,DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE,Code.eval]

/-- The complete positive one-in-three SAT assembly, including syntax checking,
is a program of the polynomially bounded certificate language. -/
def certified : CertifiedReduction Concrete.MONOTONE_ONE_IN_THREE_SAT3
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE := ⟨code,code_correct⟩

end GridHardness.PlanarSatCode
