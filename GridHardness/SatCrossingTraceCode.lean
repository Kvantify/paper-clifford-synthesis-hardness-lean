/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrderCode
public import GridHardness.LatticeRouteCodeLists
public import GridHardness.CorrectedSatIntervalPermutationWirePlacement

/-!
# SAT Crossing Trace Code

Exact chronological crossing enumeration from SAT syntax. The outer loop
uses increasing occurrence indices; each row uses increasing earlier indices.
The chronological trace determines the vertex numbering.
-/

@[expose] public section

namespace GridHardness.SatCrossingTraceCode
open CliffordComplexity GridProblems GridProblems.GridCode PlanarSatAssembly
open CorrectedSatInterval LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev RowTy := Ty.pair SatTy .nat
abbrev CellsTy := SatCrossingCode.PairListTy

def rankValue : Code RowTy .nat :=
  .comp (.pair (.comp .fst SatClauseOrderCode.permutation) .snd) (lookupNat .nat .id)

theorem rankValue_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    rankValue.eval (x,i.val)=(SatClauseOrder.permutation (finiteFormula x) i).val := by
  change (lookupNat .nat .id).eval (SatClauseOrderCode.permutation.eval x,i.val)=_
  rw [lookupNat_eval .nat .id _ _ (by rw [SatClauseOrderCode.permutation_length]; exact i.isLt)]
  exact SatClauseOrderCode.permutation_get x i

def requestTest : Code (.pair RowTy .nat) .bool :=
  Code.lt (.comp .fst rankValue) (.comp (.pair (.comp .fst .fst) .snd) rankValue)

def rowRequests : Code RowTy (.list .nat) :=
  .comp (.pair .id (.comp (.comp (.pair (.comp .fst SatClauseOrderCode.permutation) .snd)
    (takeCode .nat)) Code.indices)) (Code.filterEnv requestTest)

theorem rowRequests_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    rowRequests.eval (x,j.val)=requests
      (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) j.val := by
  change (Code.filterEnv requestTest).eval ((x,j.val),
    Code.indices.eval ((takeCode .nat).eval (SatClauseOrderCode.permutation.eval x,j.val)))=_
  rw [filterEnv_eval,takeCode_eval,indices_eval,List.length_take,
    SatClauseOrderCode.permutation_length,Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  unfold requests
  apply List.filter_congr
  intro i hi
  have hij : i<j.val := List.mem_range.mp hi
  let fi : Fin (3*x.length) := ⟨i,lt_trans hij j.isLt⟩
  change Code.natLt.eval (rankValue.eval (x,j.val),rankValue.eval (x,fi.val))=_
  rw [rankValue_eval,rankValue_eval]
  have hhj := permutationHeight_apply (SatClauseOrder.permutation (finiteFormula x)) j
  have hhi := permutationHeight_apply (SatClauseOrder.permutation (finiteFormula x)) fi
  rw [hhj,hhi]
  apply Bool.eq_iff_iff.mpr
  rw [natLt_eval_true,decide_eq_true_eq]
  omega

attribute [local irreducible] rowRequests SatClauseOrderCode.permutation

def row : Code RowTy CellsTy :=
  .comp (.pair .snd rowRequests) (.listMapEnv (.pair .snd .fst))

theorem row_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    row.eval (x,j.val)=(requests
      (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) j.val).map
        (fun i => (i,j.val)) := by
  change (rowRequests.eval (x,j.val)).map (fun i => (i,j.val))=_
  rw [rowRequests_eval]

attribute [local irreducible] row

def code : Code SatTy CellsTy :=
  .comp (.pair .id (.comp SatClauseOrderCode.permutation Code.indices))
    (.comp (.listMapEnv row) .listJoin)

theorem trace_flatMap (height : Nat →Nat) (n : Nat) : ∀j,
    trace height n j=(List.range n).flatMap
      (fun k => (requests height (j+k)).map (fun i => (i,j+k))) := by
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    rw [trace,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,ih]
    simp only [Nat.add_zero,Function.comp_def,Nat.add_assoc,Nat.add_comm 1]

theorem code_eval (x : SatTy.denote) : code.eval x=
    trace (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) (3*x.length) 0 := by
  change ((Code.indices.eval (SatClauseOrderCode.permutation.eval x)).map
    (fun j => row.eval (x,j))).flatten=_
  rw [indices_eval,SatClauseOrderCode.permutation_length,← List.flatMap_def,trace_flatMap]
  apply List.flatMap_congr
  intro j hj
  have hj' : j<3*x.length := List.mem_range.mp hj
  simpa only [Nat.zero_add] using row_eval x ⟨j,hj'⟩

/-- Sum the unique matching index; absence returns zero. -/
def indexTest : Code (.pair SatCrossingCode.PairTy (.pair SatCrossingCode.PairTy .nat)) .bool :=
  .comp (.pair (.comp .snd .fst) .fst) Code.natPairEq

def lookupIndex : Code (.pair CellsTy SatCrossingCode.PairTy) .nat :=
  .comp (.pair .snd (.comp .fst .listEnum))
    (.comp (Code.filterEnv indexTest) (.comp (.listMap .snd) .listSum))

theorem lookupIndex_eval (xs : List (Nat ×Nat)) (q : Nat ×Nat) :
    lookupIndex.eval (xs,q)=(((xs.zipIdx).filter (fun r => decide (r.1=q))).map Prod.snd).sum := by
  change (((Code.filterEnv indexTest).eval (q,xs.zipIdx)).map Prod.snd).sum=_
  rw [filterEnv_eval]
  congr 2

def traceIndex : Code (.pair SatTy SatCrossingCode.PairTy) .nat :=
  .comp (.pair (.comp .fst code) .snd) lookupIndex

theorem index_sum (xs : List (Nat ×Nat)) (hn : xs.Nodup) (q : Nat ×Nat) (hq : q ∈xs) :
    (((xs.zipIdx).filter (fun r => decide (r.1=q))).map Prod.snd).sum=xs.idxOf q := by
  have hz : xs.zipIdx.Nodup := by
    apply List.Nodup.of_map (f:=Prod.fst)
    simpa only [List.zipIdx_map_fst] using hn
  have hp : ((xs.zipIdx).filter (fun r => decide (r.1=q))).Perm [(q,xs.idxOf q)] := by
    apply (List.perm_ext_iff_of_nodup (hz.filter _) (by simp)).mpr
    rintro ⟨v,i⟩
    simp only [List.mem_filter,List.mem_zipIdx_iff_getElem?,decide_eq_true_eq,List.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hi,rfl⟩
      obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hi
      exact ⟨rfl,(hn.idxOf_getElem i hi).symm.trans (congrArg (fun z => xs.idxOf z) he)⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨List.getElem?_idxOf hq,rfl⟩
  simpa using (hp.map Prod.snd).sum_eq

theorem traceIndex_eval (x : SatTy.denote)
    (c : WireCrossingSchedule.Cell (SatClauseOrder.permutation (finiteFormula x))) :
    traceIndex.eval (x,(c.val.1.val,c.val.2.val))=
      (trace (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) (3*x.length) 0).idxOf
        (c.val.1.val,c.val.2.val) := by
  change lookupIndex.eval (code.eval x,(c.val.1.val,c.val.2.val))=_
  rw [lookupIndex_eval,code_eval]
  exact index_sum _ (trace_nodup _ _ _) _
    ((PermutationGraph.covers_inversion _ _ _).mpr c.property)

end GridHardness.SatCrossingTraceCode
