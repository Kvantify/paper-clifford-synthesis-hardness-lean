/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatReduction
public import GridHardness.DirectedToBipartiteCode
public import CliffordComplexity.Numbering
import Mathlib.Data.List.GetD

/-!
# Planar SAT Code Assembly

Number SAT vertices and compile the variable, clause, and occurrence arcs as
polynomial-time programs on the framed formula encoding.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PlanarSatCode
open CliffordComplexity PlanarSatAssembly

abbrev PairTy := Ty.pair .nat .nat
abbrev EdgesTy := Ty.list PairTy
abbrev OccTy := PairTy

/-- Number every vertex tag in consecutive finite blocks. -/
def numbering (n m : Nat) : Numbering (Vertex n m) :=
  (Numbering.fin 3).sum (((Numbering.fin n).prod Numbering.bool).sum
    (((Numbering.fin m).prod (Numbering.fin 12)).sum
      (((Numbering.fin m).prod (Numbering.fin 3)).prod (Numbering.fin 8))))

@[simp] theorem numbering_size (n m : Nat) : (numbering n m).size = 3 + n*2 + m*12 + m*3*8 := by
  simp [numbering,Nat.add_assoc]

@[simp] theorem numbering_sent {n m : Nat} (i : Fin 3) : (numbering n m).num (sent i) = i.val := rfl
@[simp] theorem numbering_var {n m : Nat} (v : Fin n) (b : Bool) :
    (numbering n m).num (var v b) = 3 + (v.val*2 + b.toNat) := by
  cases b <;> rfl
@[simp] theorem numbering_clause {n m : Nat} (c : Fin m) (j : Fin 12) :
    (numbering n m).num (clause c j) = 3 + (n*2 + (c.val*12+j.val)) := rfl
@[simp] theorem numbering_xor {n m : Nat} (o : Occurrence m) (j : Fin 8) :
    (numbering n m).num (xor o j) = 3 + (n*2 + (m*12 + ((o.1.val*3+o.2.val)*8+j.val))) := rfl

/-- Zip two lists by their enumerated positions; a polynomial nested loop. -/
def zipCode (σ τ : Ty) : Code (.pair (.list σ) (.list τ)) (.list (.pair σ τ)) :=
  .comp (.pair (.comp .fst .listEnum) (.comp .snd .listEnum))
    (.comp Code.cross
      (.comp (.listFilter (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq))
        (.listMap (.pair (.comp .fst .fst) (.comp .snd .fst)))))

theorem mem_zipCode {σ τ : Ty} (xs : List σ.denote) (ys : List τ.denote) (a : σ.denote) (b : τ.denote) :
    (a,b) ∈ (zipCode σ τ).eval (xs,ys) ↔ (a,b) ∈ xs.zip ys := by
  change (a,b) ∈ (((Code.cross (σ := .pair σ .nat) (τ := .pair τ .nat)).eval (xs.zipIdx,ys.zipIdx)).filter
    (fun p => decide (p.1.2 = p.2.2))).map (fun p => (p.1.1,p.2.1)) ↔ _
  simp only [List.mem_map,List.mem_filter,mem_cross_eval (σ := .pair σ .nat) (τ := .pair τ .nat),decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨a',i⟩,⟨b',j⟩⟩,⟨⟨ha,hb⟩,hij⟩,he⟩
    dsimp at ha hb hij he ⊢
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    subst j
    obtain ⟨hi,hai⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp ha)
    obtain ⟨hj,hbj⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hb)
    apply List.mem_iff_getElem.mpr
    refine ⟨i,by simp; omega,?_⟩
    simp only [List.getElem_zip]
    exact Prod.ext hai hbj
  · intro h
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    have hmin : i < xs.length ∧ i < ys.length := by simpa only [List.length_zip,lt_min_iff] using hi
    have hix := hmin.1
    have hiy := hmin.2
    rw [List.getElem_zip] at he
    refine ⟨((a,i),(b,i)),⟨⟨?_,?_⟩,rfl⟩,rfl⟩
    · apply List.mem_zipIdx_iff_getElem?.mpr
      exact List.getElem?_eq_some_iff.mpr ⟨hix,congrArg Prod.fst he⟩
    · apply List.mem_zipIdx_iff_getElem?.mpr
      exact List.getElem?_eq_some_iff.mpr ⟨hiy,congrArg Prod.snd he⟩

/-- Drop the first list position by filtering its enumeration. -/
def tailCode (τ : Ty) : Code (.list τ) (.list τ) :=
  .comp .listEnum (.comp (.listFilter (.comp (.pair (.const .nat 1) .snd) .natLe)) (.listMap .fst))

theorem tailCode_eval {τ : Ty} (xs : List τ.denote) : (tailCode τ).eval xs = xs.tail := by
  have hf : ∀ (ys : List τ.denote) (s : Nat), 1 ≤ s →
      (ys.zipIdx s).filter (fun p => decide (1 ≤ p.2)) = ys.zipIdx s := by
    intro ys
    induction ys with
    | nil => intro s hs; rfl
    | cons y ys ih =>
      intro s hs
      simp [List.zipIdx_cons,hs,ih (s+1) (by omega)]
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp [tailCode,Code.eval,List.zipIdx_cons,hf xs 1 (by omega)]

/-- Compile a fixed finite table of expressions. The table is part of the program. -/
def table {A : Type*} {σ τ : Ty} (xs : List A) (f : A → Code σ τ) : Code σ (.list τ) :=
  xs.foldr (fun a acc => Code.cons (f a) acc) (.const (.list τ) [])

theorem table_eval {A : Type*} {σ τ : Ty} (xs : List A) (f : A → Code σ τ) (x : σ.denote) :
    (table xs f).eval x = xs.map (fun a => (f a).eval x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a).eval x :: (table xs f).eval x = _
    rw [ih]
    rfl

def varPool : Code SatTy (.list .nat) := Code.append varsCode (.const (.list .nat) [0])
def varCount : Code SatTy .nat := .comp varPool .listLen
def variableIndices : Code SatTy (.list .nat) := .comp varPool Code.indices
def clauses : Code SatTy (.list .nat) := Code.indices

def occurrencesCode : Code SatTy (.list OccTy) :=
  .comp (.pair clauses (.const (.list .nat) [0,1,2])) Code.cross

def varNum (b : Bool) : Code .nat .nat :=
  Code.add (.const .nat 3) (Code.add (Code.mul .id (.const .nat 2)) (.const .nat b.toNat))

def clauseNum (j : Nat) : Code (.pair SatTy .nat) .nat :=
  Code.add (.const .nat 3)
    (Code.add (Code.mul (.comp .fst varCount) (.const .nat 2))
      (Code.add (Code.mul .snd (.const .nat 12)) (.const .nat j)))

def xorNum (j : Nat) : Code (.pair SatTy OccTy) .nat :=
  Code.add (.const .nat 3)
    (Code.add (Code.mul (.comp .fst varCount) (.const .nat 2))
      (Code.add (Code.mul (.comp .fst .listLen) (.const .nat 12))
        (Code.add (Code.mul (Code.add (Code.mul (.comp .snd .fst) (.const .nat 3))
          (.comp .snd .snd)) (.const .nat 8)) (.const .nat j))))

def slotsCode : Code SatTy (.list PairTy) :=
  Code.append (Code.append (.const (.list PairTy) [(0,2)])
    (.comp variableIndices (.listMap (.pair (varNum false) (varNum true)))))
    (.comp (.pair .id clauses) (.listMapEnv (.pair (clauseNum 8) (clauseNum 1))))

def backboneCode : Code SatTy EdgesTy :=
  .comp (.pair (.comp slotsCode (.listMap .snd))
    (Code.append (.comp slotsCode (.comp (.listMap .fst) (tailCode .nat)))
      (.const (.list .nat) [0]))) (zipCode .nat .nat)

/-- Total lookup of an occurrence's literal label, with zero for missing syntax. -/
def literalAt : Code (.pair SatTy OccTy) .nat :=
  .comp (.pair
      (.comp (.pair .fst (.comp .snd .fst)) (.comp Code.listNth .listJoin))
      (.comp .snd .snd))
    (.comp Code.listNth (.comp (.listMap .fst) .listSum))

def slotAt : Code (.pair SatTy OccTy) .nat :=
  .comp (.pair (.comp .fst varsCode) literalAt) slotOfCode

def occurrenceTest : Code (.pair (.pair SatTy .nat) OccTy) .bool :=
  .comp (.pair (.comp (.pair (.comp .fst .fst) .snd) slotAt) (.comp .fst .snd)) .natEq

def occurrencesFor : Code (.pair SatTy .nat) (.list OccTy) :=
  .comp (.pair .id (.comp .fst occurrencesCode)) (Code.filterEnv occurrenceTest)

def variableChainCode : Code (.pair SatTy .nat) EdgesTy :=
  .comp (.pair
    (Code.cons (.comp .snd (varNum false))
      (.comp (.pair .fst occurrencesFor) (.listMapEnv (xorNum 0))))
    (Code.append (.comp (.pair .fst occurrencesFor) (.listMapEnv (xorNum 3)))
      (.comp (.comp .snd (varNum true)) .listSingle))) (zipCode .nat .nat)

def variableEdgesAt : Code (.pair SatTy .nat) EdgesTy :=
  Code.cons (.pair (.comp .snd (varNum false)) (.comp .snd (varNum true))) variableChainCode

def variableEdgesCode : Code SatTy EdgesTy :=
  .comp (.pair .id variableIndices) (.comp (.listMapEnv variableEdgesAt) .listJoin)

def clauseEdgesAt : Code (.pair SatTy .nat) EdgesTy :=
  table clauseBody (fun e => .pair (clauseNum e.1.val) (clauseNum e.2.val))

def clauseEdgesCode : Code SatTy EdgesTy :=
  .comp (.pair .id clauses) (.comp (.listMapEnv clauseEdgesAt) .listJoin)

def clausePortNum (top : Bool) : Code (.pair SatTy OccTy) .nat :=
  Code.add (.const .nat 3)
    (Code.add (Code.mul (.comp .fst varCount) (.const .nat 2))
      (Code.add (Code.mul (.comp .snd .fst) (.const .nat 12))
        (Code.add (Code.mul (.comp .snd .snd) (.const .nat 4)) (.const .nat top.toNat))))

def occurrenceEdgesAt : Code (.pair SatTy OccTy) EdgesTy :=
  Code.append (table [false,true] (fun b =>
    if b then .pair (xorNum 7) (clausePortNum true)
    else .pair (clausePortNum false) (xorNum 4)))
    (table (List.finRange 10) (fun e => .pair (xorNum (XorGadget.arc e).1.val)
      (xorNum (XorGadget.arc e).2.val)))

def occurrenceEdgesCode : Code SatTy EdgesTy :=
  .comp (.pair .id occurrencesCode) (.comp (.listMapEnv occurrenceEdgesAt) .listJoin)

def edgesCode : Code SatTy EdgesTy :=
  Code.append (Code.append (Code.append
    (Code.append (.const EdgesTy [(0,1),(1,2)]) backboneCode) variableEdgesCode)
      clauseEdgesCode) occurrenceEdgesCode

/-- Produce a vertex list by bounded iteration: three sentinels, two slots
per listed variable position, and thirty-six per clause. -/
def verticesCode : Code SatTy (.list .nat) :=
  Code.append (Code.append (.const (.list .nat) [0,0,0])
    (.comp varPool (.comp (.listMap (.const (.list .nat) [0,0])) .listJoin)))
    (.comp .id (.comp (.listMap (.const (.list .nat) (List.replicate 36 0))) .listJoin))

def assembly : Code SatTy GraphTy :=
  .pair verticesCode (.pair edgesCode (.const .nat 0))

@[simp] theorem varCount_eval (x : SatTy.denote) : varCount.eval x = (vsOf x).length+1 := by
  change (varsCode.eval x ++ [0]).length = _
  rw [varsCode_eval]
  simp

@[simp] theorem variableIndices_eval (x : SatTy.denote) : variableIndices.eval x = List.range ((vsOf x).length+1) := by
  rw [variableIndices,Code.eval,indices_eval]
  change List.range (varCount.eval x) = _
  rw [varCount_eval]

@[simp] theorem clauses_eval (x : SatTy.denote) : clauses.eval x = List.range x.length := indices_eval x

@[simp] theorem varNum_eval (b : Bool) (v : Nat) : (varNum b).eval v = 3+(v*2+b.toNat) := rfl
@[simp] theorem clauseNum_eval (j : Nat) (x : SatTy.denote) (c : Nat) :
    (clauseNum j).eval (x,c) = 3+(((vsOf x).length+1)*2+(c*12+j)) := by
  change 3+(varCount.eval x*2+(c*12+j)) = _
  rw [varCount_eval]
@[simp] theorem xorNum_eval (j : Nat) (x : SatTy.denote) (o : Nat ×Nat) :
    (xorNum j).eval (x,o) = 3+(((vsOf x).length+1)*2+(x.length*12+((o.1*3+o.2)*8+j))) := by
  change 3+(varCount.eval x*2+(x.length*12+((o.1*3+o.2)*8+j))) = _
  rw [varCount_eval]

theorem verticesCode_length (x : SatTy.denote) :
    (verticesCode.eval x).length = (numbering ((vsOf x).length+1) x.length).size := by
  change (List.replicate 3 0 ++ ((varPool.eval x).map (fun _ => [0,0])).flatten ++
    (x.map (fun _ => List.replicate 36 0)).flatten).length = _
  simp [List.length_flatten,numbering_size]
  have hn : (varPool.eval x).length = (vsOf x).length+1 := varCount_eval x
  rw [hn]
  omega

theorem variableIndices_finite (x : SatTy.denote) : variableIndices.eval x =
    (List.finRange ((vsOf x).length+1)).map Fin.val := by simp

theorem clauses_finite (x : SatTy.denote) : clauses.eval x =
    (List.finRange x.length).map Fin.val := by simp

def occVal {m : Nat} (o : Occurrence m) : Nat × Nat := (o.1.val,o.2.val)

theorem occurrencesCode_eval (x : SatTy.denote) : occurrencesCode.eval x =
    (occurrences x.length).map occVal := by
  change ((clauses.eval x).map (fun c => [0,1,2].map (fun j => (c,j)))).flatten = _
  rw [clauses_finite]
  simp only [← List.flatMap_def,List.flatMap_map,occurrences,List.map_flatMap,List.map_map]
  apply List.flatMap_congr
  intro c _
  rfl

theorem literalAt_eval (x : SatTy.denote) (c : Fin x.length) (j : Nat) :
    literalAt.eval (x,(c.val,j)) = ((x.get c).getD j (0,true)).1 := by
  change (((Code.listNth (τ := .pair .nat .bool)).eval
    (((Code.listNth (τ := .list (.pair .nat .bool))).eval (x,c.val)).flatten,j)).map Prod.fst).sum = _
  rw [listNth_eval c.isLt]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  change (((Code.listNth (τ := .pair .nat .bool)).eval (x.get c,j)).map Prod.fst).sum = _
  by_cases hj : j < (x.get c).length
  · rw [listNth_eval hj]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    change (x.get c)[j].1 = ((x.get c).getD j (0,true)).1
    rw [List.getD_eq_getElem _ _ hj]
  · rw [listNth_eval_of_le (Nat.le_of_not_lt hj)]
    simp only [List.map_nil,List.sum_nil]
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]

theorem slotAt_eval (x : SatTy.denote) (o : Occurrence x.length) :
    slotAt.eval (x,occVal o) = (finiteFormula x o.1 o.2).val := by
  change slotOfCode.eval (varsCode.eval x,literalAt.eval (x,occVal o)) = _
  rw [varsCode_eval]
  change slotOfCode.eval (vsOf x,literalAt.eval (x,(o.1.val,o.2.val))) = _
  rw [literalAt_eval,slotOfCode_eval]
  rfl

theorem occurrenceTest_eval (x : SatTy.denote) (v : Nat) (o : Nat ×Nat) :
    occurrenceTest.eval ((x,v),o) = decide (slotAt.eval (x,o) = v) := rfl

set_option backward.isDefEq.respectTransparency true in
theorem occurrencesFor_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    occurrencesFor.eval (x,v.val) = (occurrencesOf (finiteFormula x) v).map occVal := by
  unfold occurrencesFor
  rw [Code.eval,Code.eval,Code.eval,Code.eval,Code.eval]
  rw [filterEnv_eval,occurrencesCode_eval,List.filter_map]
  simp only [Function.comp_def,occurrenceTest_eval]
  apply congrArg (List.map occVal)
  apply List.filter_congr
  intro o ho
  change occurrenceTest.eval ((x,v.val),occVal o) = decide (finiteFormula x o.1 o.2 = v)
  exact (occurrenceTest_eval x v.val (occVal o)).trans (by
    rw [slotAt_eval]
    simp only [Fin.val_inj])

set_option backward.isDefEq.respectTransparency true

theorem slotsCode_eval (x : SatTy.denote) : slotsCode.eval x =
    (slots ((vsOf x).length+1) x.length).map
      (fun p => ((numbering _ _).num p.1,(numbering _ _).num p.2)) := by
  change [(0,2)] ++ (variableIndices.eval x).map (fun v => ((varNum false).eval v,(varNum true).eval v)) ++
    (clauses.eval x).map (fun c => ((clauseNum 8).eval (x,c),(clauseNum 1).eval (x,c))) = _
  rw [variableIndices_finite,clauses_finite]
  simp only [slots,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    numbering_sent,numbering_var,numbering_clause,varNum_eval,clauseNum_eval (x := x)]
  rfl

set_option maxHeartbeats 1000000 in
-- Evaluating the nested program combinators exposes the numbered SAT edges.
/-- The emitted backbone edges coincide with the numbered abstract backbone. -/
theorem mem_backboneCode (x : SatTy.denote)
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ backboneCode.eval x ↔
      (a,b) ∈ backbone ((vsOf x).length+1) x.length := by
  change _ ∈ (zipCode .nat .nat).eval ((slotsCode.eval x).map Prod.snd,
    (tailCode .nat).eval ((slotsCode.eval x).map Prod.fst) ++ [0]) ↔ _
  rw [mem_zipCode,tailCode_eval,slotsCode_eval]
  simp only [List.map_map,Function.comp_def]
  have hs : ((slots ((vsOf x).length+1) x.length).map
      (fun p => (numbering _ _).num p.1)).tail ++ [0] =
      (((slots ((vsOf x).length+1) x.length).map Prod.fst).tail ++ [sent 0]).map
        (numbering _ _).num := by
    simp [List.map_append,List.map_tail,List.map_map,Function.comp_def]
  rw [hs]
  have hs2 : (slots ((vsOf x).length+1) x.length).map (fun p => (numbering _ _).num p.2) =
      ((slots ((vsOf x).length+1) x.length).map Prod.snd).map (numbering _ _).num := by
    rw [List.map_map]
    rfl
  rw [hs2]
  rw [List.zip_map]
  exact (numbering _ _).mem_map_num_pair

set_option maxHeartbeats 1000000 in
-- Evaluating the nested program combinators exposes the numbered SAT edges.
/-- The filtered occurrence list yields exactly the intended numbered chain links. -/
theorem mem_variableChainCode (x : SatTy.denote) (v : Fin ((vsOf x).length +1))
    (a b : Vertex ((vsOf x).length +1) x.length) :
    ((numbering _ _).num a,(numbering _ _).num b) ∈ variableChainCode.eval (x,v.val) ↔
      (a,b) ∈ variableChain (finiteFormula x) v := by
  change _ ∈ (zipCode .nat .nat).eval
    ((varNum false).eval v.val :: (occurrencesFor.eval (x,v.val)).map (fun o => (xorNum 0).eval (x,o)),
      (occurrencesFor.eval (x,v.val)).map (fun o => (xorNum 3).eval (x,o)) ++ [(varNum true).eval v.val]) ↔ _
  rw [mem_zipCode,occurrencesFor_eval]
  simp only [List.map_map,Function.comp_def,varNum_eval,xorNum_eval (x := x)]
  have hs : (3+(v.val*2+false.toNat)) ::
      ((occurrencesOf (finiteFormula x) v).map fun o =>
        3+(((vsOf x).length+1)*2+(x.length*12+(((occVal o).1*3+(occVal o).2)*8+0)))) =
      (var v false :: (occurrencesOf (finiteFormula x) v).map (fun o => PlanarSatAssembly.xor o 0)).map
        (numbering _ _).num := by simp [occVal,Function.comp_def]
  have ht : ((occurrencesOf (finiteFormula x) v).map fun o =>
        3+(((vsOf x).length+1)*2+(x.length*12+(((occVal o).1*3+(occVal o).2)*8+3)))) ++ [3+(v.val*2+true.toNat)] =
      ((occurrencesOf (finiteFormula x) v).map (fun o => PlanarSatAssembly.xor o 3) ++ [var v true]).map
        (numbering _ _).num := by simp [occVal,Function.comp_def]
  rw [hs,ht,List.zip_map]
  exact (numbering _ _).mem_map_num_pair

theorem clauseEdgesAt_eval (x : SatTy.denote) (c : Fin x.length) :
    clauseEdgesAt.eval (x,c.val) = (clauseEdges (n := (vsOf x).length+1) c).map
      (fun p => ((numbering _ _).num p.1,(numbering _ _).num p.2)) := by
  rw [clauseEdgesAt,table_eval]
  simp only [Code.eval,clauseNum_eval (x := x),clauseEdges,List.map_map,Function.comp_def,numbering_clause]

theorem clausePortNum_eval (top : Bool) (x : SatTy.denote) (o : Occurrence x.length) :
    (clausePortNum top).eval (x,occVal o) =
      (numbering ((vsOf x).length+1) x.length).num
        (clause o.1 (if top then clauseTop o.2 else clauseBottom o.2)) := by
  change 3+(varCount.eval x*2+(o.1.val*12+(o.2.val*4+top.toNat))) = _
  rw [varCount_eval,numbering_clause]
  rcases o with ⟨c,j⟩
  fin_cases j <;> cases top <;> rfl

set_option maxHeartbeats 1000000 in
-- Evaluating the nested program combinators exposes the numbered SAT edges.
theorem occurrenceEdgesAt_eval (x : SatTy.denote) (o : Occurrence x.length) :
    occurrenceEdgesAt.eval (x,occVal o) =
      (clauseLinks (n := (vsOf x).length+1) o ++ xorEdges (n := (vsOf x).length+1) o).map
        (fun p => ((numbering _ _).num p.1,(numbering _ _).num p.2)) := by
  have hx (j : Fin 8) : (xorNum j.val).eval (x,occVal o) =
      (numbering ((vsOf x).length+1) x.length).num (xor o j) := by
    rw [xorNum_eval]
    rfl
  have h4 : (xorNum 4).eval (x,occVal o) = (numbering ((vsOf x).length+1) x.length).num (xor o 4) := hx 4
  have h7 : (xorNum 7).eval (x,occVal o) = (numbering ((vsOf x).length+1) x.length).num (xor o 7) := hx 7
  have hb := clausePortNum_eval false x o
  have ht := clausePortNum_eval true x o
  rw [occurrenceEdgesAt, append_eval, table_eval, table_eval, List.map_append]
  congr 1
  · change [((clausePortNum false).eval (x,occVal o),(xorNum 4).eval (x,occVal o)),
      ((xorNum 7).eval (x,occVal o),(clausePortNum true).eval (x,occVal o))] = _
    rw [hb,ht,h4,h7]
    rfl
  · simp only [xorEdges,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro e he
    change ((xorNum (XorGadget.arc e).1.val).eval (x,occVal o),
      (xorNum (XorGadget.arc e).2.val).eval (x,occVal o)) = _
    rw [hx,hx]

end GridHardness.PlanarSatCode
