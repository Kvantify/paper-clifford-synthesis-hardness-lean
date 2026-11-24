/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCodeLists
public import GridHardness.LatticeRouteTrim

/-!
# Lattice Route Orientation Code

Explicit bounded-list programs for route reversal, orientation and cuts.
Binary cut lengths restrict an existing list; they never create loop ranges.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCoreCode
open CliffordComplexity LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Reverse by reading the complementary positions of an explicit enumeration. -/
def reverseCode (τ : Ty) : Code (.list τ) (.list τ) :=
  .comp (.pair .id Code.indices)
    (.comp (.listMapEnv
      (.comp (.pair .fst
        (.comp (.pair (.comp (.pair (.comp .fst .listLen) (.const .nat 1)) .natSub) .snd) .natSub))
        Code.listNth)) .listJoin)

def reverseScan {α : Type*} (xs : List α) : List α :=
  (List.range xs.length).flatMap (fun i => xs[xs.length-1-i]?.toList)

theorem reverseScan_eq {α : Type*} (xs : List α) : reverseScan xs=xs.reverse := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    unfold reverseScan at *
    rw [List.length_cons,Nat.add_sub_cancel,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,Nat.sub_self,List.getElem?_cons_zero,
      Option.toList_some,List.append_nil]
    rw [List.reverse_cons,← ih]
    congr 1
    apply List.flatMap_congr
    intro i hi
    have hi' : i<xs.length := List.mem_range.mp hi
    have he : xs.length-i=(xs.length-1-i)+1 := by omega
    rw [he,List.getElem?_cons_succ]

theorem reverseCode_eval {τ : Ty} (xs : List τ.denote) :
    (reverseCode τ).eval xs=xs.reverse := by
  change ((Code.indices.eval xs).map (fun i =>
    (Code.listNth (τ:=τ)).eval (xs,xs.length-1-i))).flatten=_
  rw [indices_eval,← List.flatMap_def,← reverseScan_eq]
  apply List.flatMap_congr
  intro i _
  exact listNth_option xs (xs.length-1-i)

/-- Choose either the existing order or its explicit reversal. -/
def orientCode (τ : Ty) : Code (.pair (.list τ) .bool) (.list τ) :=
  .branch .snd (.comp .fst (reverseCode τ)) .fst

theorem orientCode_eval {τ : Ty} (xs : List τ.denote) (b : Bool) :
    (orientCode τ).eval (xs,b)=(if b then xs.reverse else xs) := by
  cases b
  · rfl
  · exact reverseCode_eval xs

/-- Drop a fixed initial cut and an input terminal cut. -/
def trimCode (τ : Ty) (a : Nat) : Code (.pair (.list τ) .nat) (.list τ) :=
  .comp (.pair (.comp (.pair .fst (.const .nat a)) (dropCode τ))
    (.comp (.pair (.comp (.pair (.comp .fst .listLen) (.const .nat a)) .natSub) .snd) .natSub))
    (takeCode τ)

theorem trimCode_eval {τ : Ty} (a b : Nat) (xs : List τ.denote) :
    (trimCode τ a).eval (xs,b)=LatticeRouteTrim.trim a b xs := by
  change (takeCode τ).eval ((dropCode τ).eval (xs,a),xs.length-a-b)=_
  rw [takeCode_eval,dropCode_eval]
  rfl

theorem trim_map {α β : Type*} (a b : Nat) (f : α →β) (xs : List α) :
    LatticeRouteTrim.trim a b (xs.map f)=(LatticeRouteTrim.trim a b xs).map f := by
  simp only [LatticeRouteTrim.trim,List.length_map,← List.map_drop,← List.map_take]

end GridHardness.LatticeRouteCoreCode
