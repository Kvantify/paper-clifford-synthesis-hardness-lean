/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCodeLists
public import GridHardness.LatticeRouteRuns

/-!
# Lattice Route Directions Code

Executable cardinal directions of encoded lattice routes. Signed-coordinate
comparisons work on redundant as well as canonical integer encodings.
-/

@[expose] public section

namespace GridHardness.LatticeRouteDirectionsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Test that the second signed integer is the first plus one. -/
def successorEq : Code (.pair SignedTy SignedTy) .bool :=
  .comp (.pair
    (Code.add (Code.add (.comp .fst .fst) (.comp .snd .snd)) (.const .nat 1))
    (Code.add (.comp .snd .fst) (.comp .fst .snd))) .natEq

theorem successorEq_eval (p q : SignedTy.denote) :
    successorEq.eval (p,q)=decide (integer q=integer p+1) := by
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  apply Bool.eq_iff_iff.mpr
  change decide (a+d+1=c+b)=true ↔ decide ((c : Int)-d=(a : Int)-b+1)=true
  simp only [decide_eq_true_eq]
  exact (show ∀ a b c d : Nat, a+d+1=c+b ↔ (c : Int)-d=(a : Int)-b+1 from
    by intro a b c d; omega) a b c d

/-- Direction values 0,1,2,3 are east,north,west,south, exactly as in the
semantic total direction function (including non-unit input pairs). -/
def directionCode : Code (.pair PointTy PointTy) .nat :=
  .branch (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) successorEq) (.const .nat 0)
    (.branch (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) successorEq) (.const .nat 1)
      (.branch (.comp (.pair (.comp .snd .fst) (.comp .fst .fst)) successorEq)
        (.const .nat 2) (.const .nat 3)))

theorem directionCode_eval (p q : PointTy.denote) :
    directionCode.eval (p,q)=(LatticeRouteDirections.direction (decoded p) (decoded q)).val := by
  change (if successorEq.eval (p.1,q.1) then 0 else if successorEq.eval (p.2,q.2) then 1
    else if successorEq.eval (q.1,p.1) then 2 else 3)=_
  rw [successorEq_eval,successorEq_eval,successorEq_eval]
  have he : integer p.1=integer q.1+1 ↔ integer q.1=integer p.1-1 := by omega
  simp only [LatticeRouteDirections.direction,decoded,he,decide_eq_true_eq]
  split_ifs <;> simp_all

abbrev AtTy := Ty.pair CycleInputTy (.pair PointTy .nat)

/-- Emit the direction to the next point; the last point emits nothing. -/
def nextDirection : Code AtTy NatListTy :=
  .comp (.pair (.comp .snd .fst)
    (.comp (.pair .fst (Code.add (.comp .snd .snd) (.const .nat 1))) Code.listNth))
    (.listMapEnv directionCode)

theorem nextDirection_eval (xs : CycleInputTy.denote) (p : PointTy.denote) (i : Nat) :
    nextDirection.eval (xs,(p,i))=
      xs[i+1]?.toList.map (fun q => (LatticeRouteDirections.direction (decoded p) (decoded q)).val) := by
  change (Code.listNth.eval (xs,i+1)).map (fun q => directionCode.eval (p,q))=_
  rw [listNth_option]
  apply List.map_congr_left
  intro q _
  exact directionCode_eval p q

/-- Enumerate consecutive point pairs without introducing a loop over coordinates. -/
def directionsCode : Code CycleInputTy NatListTy :=
  .comp (.pair .id .listEnum) (.comp (.listMapEnv nextDirection) .listJoin)

def adjacentScan {α β : Type*} (f : α → α→β) (xs : List α) : List β :=
  xs.zipIdx.flatMap (fun q => xs[q.2+1]?.toList.map (f q.1))

theorem adjacentScan_cons {α β : Type*} (f : α → α→β) (a : α) (xs : List α) :
    adjacentScan f (a::xs)=xs.head?.toList.map (f a) ++ adjacentScan f xs := by
  unfold adjacentScan
  rw [List.zipIdx_cons']
  simp only [List.flatMap_cons,List.flatMap_map,Prod.map,id_eq,
    List.getElem?_cons_succ,List.head?_eq_getElem?]

theorem adjacentScan_directions (xs : CycleInputTy.denote) :
    adjacentScan (fun p q => (LatticeRouteDirections.direction (decoded p) (decoded q)).val) xs=
      (LatticeRouteRuns.directions (xs.map decoded)).map Fin.val := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [adjacentScan_cons,ih]
    cases xs <;> rfl

theorem directionsCode_eval (xs : CycleInputTy.denote) :
    directionsCode.eval xs=(LatticeRouteRuns.directions (xs.map decoded)).map Fin.val := by
  rw [← adjacentScan_directions]
  change (xs.zipIdx.map (fun q => nextDirection.eval (xs,q))).flatten=_
  rw [← List.flatMap_def]
  apply List.flatMap_congr
  intro q _
  exact nextDirection_eval xs q.1 q.2

end GridHardness.LatticeRouteDirectionsCode
