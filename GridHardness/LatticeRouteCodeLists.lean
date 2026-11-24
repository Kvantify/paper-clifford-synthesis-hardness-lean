/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridPointCode

/-!
# Lattice Route Code Lists

Bounded-list primitives for executable lattice-route compression. Every
iteration ranges over an explicit input list, including the prefix scan used
to stop at the first unequal direction.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCodeLists
open CliffordComplexity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Keep the positions at or beyond an input index. -/
def dropCode (τ : Ty) : Code (.pair (.list τ) .nat) (.list τ) :=
  .comp (.pair .snd (.comp .fst .listEnum))
    (.comp (Code.filterEnv (.comp (.pair .fst (.comp .snd .snd)) .natLe)) (.listMap .fst))

theorem dropCode_eval {τ : Ty} (xs : List τ.denote) (n : Nat) :
    (dropCode τ).eval (xs,n)=xs.drop n := by
  have he (ys : List τ.denote) (k : Nat) : (dropCode τ).eval (ys,k)=
      (ys.zipIdx.filter (fun p => decide (k≤p.2))).map Prod.fst := by
    change (((Code.filterEnv (e:=.nat) (t:=.pair τ .nat) _).eval (k,ys.zipIdx)).map Prod.fst)=_
    rw [filterEnv_eval]
    rfl
  rw [he]
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
    rw [List.zipIdx_cons']
    cases n with
    | zero => simp [Function.comp_def]
    | succ n =>
      simp only [List.filter_cons,List.filter_map,List.map_cons,List.map_map,
        List.drop_succ_cons,Prod.map,Function.comp_def,Nat.succ_le_iff]
      simpa [Function.comp_def] using ih n

/-- Keep a prefix whose length is supplied as a binary number. The loop still
ranges only over the explicit input list. -/
def takeCode (τ : Ty) : Code (.pair (.list τ) .nat) (.list τ) :=
  .comp (.pair .snd (.comp .fst .listEnum))
    (.comp (Code.filterEnv (.comp (.pair (.comp .snd .snd) .fst) Code.natLt)) (.listMap .fst))

theorem takeCode_eval {τ : Ty} (xs : List τ.denote) (n : Nat) :
    (takeCode τ).eval (xs,n)=xs.take n := by
  have he (ys : List τ.denote) (k : Nat) : (takeCode τ).eval (ys,k)=
      (ys.zipIdx.filter (fun p => decide (p.2<k))).map Prod.fst := by
    change (((Code.filterEnv (e:=.nat) (t:=.pair τ .nat) _).eval (k,ys.zipIdx)).map Prod.fst)=_
    rw [filterEnv_eval]
    congr 2
    funext p
    exact natLt_eval _ _
  rw [he]
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
    rw [List.zipIdx_cons']
    cases n with
    | zero => simp [Function.comp_def]
    | succ n =>
      simp only [List.filter_cons,List.filter_map,List.map_cons,List.map_map,
        List.take_succ_cons,Prod.map,Function.comp_def]
      simpa [Function.comp_def] using congrArg (List.cons a) (ih n)

/-- A prefix is retained exactly until its first failed test. -/
theorem good_prefixes {α : Type*} (p : α → Bool) (xs : List α) :
    ((xs.zipIdx.filter (fun q => (xs.take (q.2+1)).all p)).map Prod.fst)=xs.takeWhile p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.zipIdx_cons']
    cases ha : p a <;>
      simp only [List.filter_cons,List.take_succ_cons,List.all_cons,ha,
        Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true,
        List.filter_map,List.map_cons,List.map_map,Function.comp_def,Prod.map,
        List.take_zero,List.all_nil,List.takeWhile_cons]
    · simp
    · simpa only [List.filter_cons,List.filter_map,List.map_map,Function.comp_def,
        List.map_cons,List.take_zero,List.all_nil,ite_true,id_eq] using congrArg (List.cons a) ih

abbrev NatListTy := Ty.list .nat

/-- Decide that every entry equals the selected direction. -/
def allEqual : Code (.pair .nat NatListTy) .bool :=
  Code.isNil (Code.filterEnv (.comp .natEq .boolNot))

theorem allEqual_eval (d : Nat) (xs : List Nat) :
    allEqual.eval (d,xs)=xs.all (fun e => decide (d=e)) := by
  apply Bool.eq_iff_iff.mpr
  rw [allEqual,isNil_eval_true,filterEnv_eval]
  simp only [Code.eval,List.filter_eq_nil_iff,Bool.not_eq_true,decide_eq_false_iff_not,
    List.all_eq_true,decide_eq_true_eq,Bool.not_eq_false']

/-- The explicit consecutive prefix of entries equal to `d`. -/
def takeEqual : Code (.pair .nat NatListTy) NatListTy :=
  .comp (.pair .id (.comp .snd .listEnum))
    (Code.filterMapEnv
      (.comp (.pair (.comp .fst .fst)
        (.comp (.pair (.comp .fst .snd)
          (Code.add (.comp .snd .snd) (.const .nat 1))) (takeCode .nat))) allEqual)
      (.comp .snd .fst))

theorem takeEqual_eval (d : Nat) (xs : List Nat) :
    takeEqual.eval (d,xs)=xs.takeWhile (fun e => decide (d=e)) := by
  change (Code.filterMapEnv (e:=.pair .nat NatListTy) (s:=.pair .nat .nat) (t:=.nat) _ _).eval ((d,xs),xs.zipIdx)=_
  rw [filterMapEnv_eval]
  have he : (fun q : Nat×Nat =>
      allEqual.eval (d,(takeCode .nat).eval (xs,q.2+1)))=
      (fun q : Nat×Nat => (xs.take (q.2+1)).all (fun e => decide (d=e))) := by
    funext q
    rw [takeCode_eval,allEqual_eval]
  change ((xs.zipIdx.filter (fun q => allEqual.eval (d,(takeCode .nat).eval (xs,q.2+1)))).map Prod.fst)=_
  rw [he,good_prefixes]

/-- Total indexing represented as a zero- or one-element list. -/
theorem listNth_option {τ : Ty} (xs : List τ.denote) (i : Nat) :
    (Code.listNth (τ:=τ)).eval (xs,i)=xs[i]?.toList := by
  by_cases hi : i<xs.length
  · rw [listNth_eval hi,List.getElem?_eq_getElem hi]
    rfl
  · rw [listNth_eval_of_le (by omega),List.getElem?_eq_none (by omega)]
    rfl

end GridHardness.LatticeRouteCodeLists
