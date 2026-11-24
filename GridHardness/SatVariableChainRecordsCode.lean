/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableChainRouteCode

/-!
# SAT Variable Chain Records Code

Numbered occurrence-chain records generated from SAT syntax. Each
nonempty variable contributes its entry, internal links, and exit; the empty
variable contributes only the separate direct body edge.
-/

@[expose] public section

namespace GridHardness.SatVariableChainRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatVariablePositionCode SatVariableChainRouteCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

def occurrenceLabel (j : Fin 8) : Code LinkTy .nat :=
  .comp (.pair (.comp .fst .fst)
    (.comp (.pair (.comp .fst PlanarSatCode.occurrencesFor) .snd) Code.listNth))
    (.comp (.listMapEnv (PlanarSatCode.xorNum j.val)) .listSum)

theorem occurrenceLabel_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1))
    (i : Fin (SatVariableOrder.count (finiteFormula x) v)) (j : Fin 8) :
    (occurrenceLabel j).eval ((x,v.val),i.val)=
      (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num
        (PlanarSatAssembly.xor (SatVariableOrder.indexedOccurrence (finiteFormula x) v i) j) := by
  change (((Code.listNth (τ:=PlanarSatCode.OccTy)).eval
    (PlanarSatCode.occurrencesFor.eval (x,v.val),i.val)).map
      (fun o => (PlanarSatCode.xorNum j.val).eval (x,o))).sum=_
  rw [PlanarSatCode.occurrencesFor_eval]
  rw [listNth_eval (by simpa only [List.length_map,SatVariableOrder.count] using i.isLt)]
  simp only [List.getElem_map,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    PlanarSatCode.xorNum_eval (x:=x),PlanarSatCode.numbering_xor,
    SatVariableOrder.indexedOccurrence,PlanarSatCode.occVal]

def sourceCode : Code LinkTy .nat :=
  .branch (.comp (.pair .snd (.const .nat 0)) .natEq)
    (.comp (.comp .fst .snd) (PlanarSatCode.varNum false))
    (.comp (.pair .fst (.comp (.pair .snd (.const .nat 1)) .natSub)) (occurrenceLabel 0))

def targetCode : Code LinkTy .nat :=
  .branch (.comp (.pair .snd (.comp .fst SatVariablePositionCode.count)) .natEq)
    (.comp (.comp .fst .snd) (PlanarSatCode.varNum true)) (occurrenceLabel 3)

def originalLabel (x : SatTy.denote) (v : PlanarSatAssembly.Vertex ((vsOf x).length +1) x.length) : Nat :=
  (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num v

theorem sourceCode_eval (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    sourceCode.eval ((x,(SatVariableChainDrawing.owner e).val),SatVariableChainDrawing.chainIndex e)=
      originalLabel x (SatVariableChainDrawing.sourceEndpoints e).1 := by
  cases e with
  | entry v h => rfl
  | between v i j h =>
    change (if i.val+1=0 then (PlanarSatCode.varNum false).eval v.val else (occurrenceLabel 0).eval ((x,v.val),i.val+1-1))=_
    simp only [Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,occurrenceLabel_eval x v i 0]
    rfl
  | exit v h =>
    simp only [sourceCode,Code.eval,SatVariableChainDrawing.owner,
      SatVariableChainDrawing.chainIndex,decide_eq_true_eq,ite_eq_right (Nat.ne_of_gt h)]
    rw [occurrenceLabel_eval x v ⟨_,by omega⟩ 0]
    rfl

theorem targetCode_eval (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    targetCode.eval ((x,(SatVariableChainDrawing.owner e).val),SatVariableChainDrawing.chainIndex e)=
      originalLabel x (SatVariableChainDrawing.sourceEndpoints e).2 := by
  cases e with
  | entry v h =>
    simp only [SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,
      targetCode,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,ite_eq_right (by omega :
        ¬0=SatVariableOrder.count (finiteFormula x) v)]
    rw [occurrenceLabel_eval x v ⟨0,h⟩ 3]
    rfl
  | between v i j h =>
    simp only [SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,
      targetCode,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,ite_eq_right (by omega :
        ¬i.val+1=SatVariableOrder.count (finiteFormula x) v)]
    rw [← h,occurrenceLabel_eval x v j 3]
    rfl
  | exit v h =>
    simp only [SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,
      targetCode,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,ite_true]
    rfl

def record (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((originalLabel x (SatVariableChainDrawing.sourceEndpoints e).1,
    originalLabel x (SatVariableChainDrawing.sourceEndpoints e).2),
    (SatVariableChainDrawing.route e).map encodePoint)

def recordAt : Code LinkTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair sourceCode targetCode) SatVariableChainRouteCode.code

theorem recordAt_eval (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    recordAt.eval ((x,(SatVariableChainDrawing.owner e).val),SatVariableChainDrawing.chainIndex e)=record x e := by
  change ((sourceCode.eval _,targetCode.eval _),SatVariableChainRouteCode.code.eval _)=_
  rw [sourceCode_eval,targetCode_eval,SatVariableChainRouteCode.code_eval]
  rfl

def link (x : SatTy.denote) (v : Fin ((vsOf x).length +1))
    (h : 0 <SatVariableOrder.count (finiteFormula x) v)
    (i : Fin (SatVariableOrder.count (finiteFormula x) v +1)) :
    SatVariableChainDrawing.Edge (finiteFormula x) :=
  if hi : i.val=0 then .entry v h
  else if he : i.val=SatVariableOrder.count (finiteFormula x) v then .exit v h
  else .between v ⟨i.val-1,by omega⟩ ⟨i.val,by omega⟩ (by change i.val=i.val-1+1; omega)

theorem link_owner (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (h : 0 <SatVariableOrder.count (finiteFormula x) v)
    (i : Fin (SatVariableOrder.count (finiteFormula x) v +1)) : SatVariableChainDrawing.owner (link x v h i)=v := by
  unfold link
  split_ifs <;> rfl

theorem link_index (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (h : 0 <SatVariableOrder.count (finiteFormula x) v)
    (i : Fin (SatVariableOrder.count (finiteFormula x) v +1)) : SatVariableChainDrawing.chainIndex (link x v h i)=i.val := by
  unfold link
  split_ifs <;> dsimp only [SatVariableChainDrawing.chainIndex] <;> omega

def edgesAt (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    List (SatVariableChainDrawing.Edge (finiteFormula x)) :=
  if h : SatVariableOrder.count (finiteFormula x) v=0 then []
  else (List.finRange (SatVariableOrder.count (finiteFormula x) v+1)).map (link x v (by omega))

def edges (x : SatTy.denote) : List (SatVariableChainDrawing.Edge (finiteFormula x)) :=
  (List.finRange ((vsOf x).length+1)).flatMap (edgesAt x)

def recordsAt : Code SatVariablePositionCode.InputTy DirectedRouteLookupCode.RecordsTy :=
  .branch (.comp (.pair SatVariablePositionCode.count (.const .nat 0)) .natEq) (.const DirectedRouteLookupCode.RecordsTy [])
    (.comp (.pair .id (.comp (Code.cons (.const PlanarSatCode.OccTy (0,0)) PlanarSatCode.occurrencesFor)
      Code.indices)) (.listMapEnv recordAt))

def code : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  .comp (.pair .id PlanarSatCode.variableIndices) (.comp (.listMapEnv recordsAt) .listJoin)

theorem recordsAt_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    recordsAt.eval (x,v.val)=(edgesAt x v).map (record x) := by
  simp only [recordsAt,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,edgesAt]
  split_ifs with h
  · rfl
  · have hp : 0<SatVariableOrder.count (finiteFormula x) v := Nat.pos_of_ne_zero h
    rw [indices_eval]
    change (List.range ((PlanarSatCode.occurrencesFor.eval (x,v.val)).length+1)).map
      (fun i => recordAt.eval ((x,v.val),i))=_
    rw [PlanarSatCode.occurrencesFor_eval,List.length_map]
    have hr : List.range (SatVariableOrder.count (finiteFormula x) v+1)=
        (List.finRange (SatVariableOrder.count (finiteFormula x) v+1)).map Fin.val := by simp
    change (List.range (SatVariableOrder.count (finiteFormula x) v+1)).map _=_
    rw [hr,List.map_map,List.map_map]
    apply List.map_congr_left
    intro i _
    have he := recordAt_eval x (link x v hp i)
    simpa only [link_owner,link_index,Function.comp_def] using he

theorem code_eval (x : SatTy.denote) : code.eval x=(edges x).map (record x) := by
  change ((PlanarSatCode.variableIndices.eval x).map (fun v => recordsAt.eval (x,v))).flatten=_
  rw [PlanarSatCode.variableIndices_finite,List.map_map,← List.flatMap_def]
  simp only [edges,List.map_flatMap]
  apply List.flatMap_congr
  exact fun v _ => recordsAt_eval x v

theorem owner_positive (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    0<SatVariableOrder.count (finiteFormula x) (SatVariableChainDrawing.owner e) := by
  cases e with
  | entry v h => exact h
  | exit v h => exact h
  | between v i j h => exact Nat.zero_lt_of_lt i.isLt

theorem index_le (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    SatVariableChainDrawing.chainIndex e<
      SatVariableOrder.count (finiteFormula x) (SatVariableChainDrawing.owner e)+1 := by
  cases e <;> simp only [SatVariableChainDrawing.chainIndex,SatVariableChainDrawing.owner]
  all_goals omega

theorem link_self (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    link x (SatVariableChainDrawing.owner e) (owner_positive x e)
      ⟨SatVariableChainDrawing.chainIndex e,index_le x e⟩=e := by
  cases e with
  | entry v h => rfl
  | exit v h => simp [link,SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,ne_of_gt h]
  | between v i j h =>
    change link x v _ ⟨i.val+1,_⟩=_
    unfold link
    rw [dite_eq_right (by omega : ¬i.val+1=0),
      dite_eq_right (by omega : i.val+1≠SatVariableOrder.count (finiteFormula x) v)]
    simp only [Nat.add_sub_cancel]
    have hj : (⟨i.val+1,by omega⟩ : Fin (SatVariableOrder.count (finiteFormula x) v))=j := Fin.ext h.symm
    simp only [hj]

theorem mem_edges (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) : e∈edges x := by
  apply List.mem_flatMap.mpr
  refine ⟨SatVariableChainDrawing.owner e,List.mem_finRange _,?_⟩
  rw [edgesAt,dite_eq_right (Nat.ne_of_gt (owner_positive x e))]
  exact List.mem_map.mpr ⟨⟨SatVariableChainDrawing.chainIndex e,index_le x e⟩,
    List.mem_finRange _,link_self x e⟩

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃ e,r=record x e := by
  rw [code_eval,List.mem_map]
  constructor
  · rintro ⟨e,_,h⟩; exact ⟨e,h.symm⟩
  · rintro ⟨e,rfl⟩; exact ⟨e,mem_edges x e,rfl⟩

end GridHardness.SatVariableChainRecordsCode
