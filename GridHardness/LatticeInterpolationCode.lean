/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridPointCode
public import GridHardness.LatticeSubdivision

/-!
# Lattice Interpolation Code

Binary signed-coordinate arithmetic for fixed lattice subdivision.
Only the program-constant scale supplies the finite interpolation table.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCoreCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Multiply a redundant signed integer by a binary natural and normalize. -/
def mulNatSigned : Code (.pair .nat SignedTy) SignedTy :=
  .comp (.pair (Code.mul .fst (.comp .snd .fst))
    (Code.mul .fst (.comp .snd .snd))) normalize

theorem mulNatSigned_eval (n : Nat) (p : SignedTy.denote) :
    mulNatSigned.eval (n,p)=encodeInt ((n : Int)*integer p) := by
  change normalize.eval (n*p.1,n*p.2)=_
  rw [normalize_eval]
  congr 1
  simp only [integer,Nat.cast_mul]
  ring

def subSigned : Code (.pair SignedTy SignedTy) SignedTy :=
  .comp (.pair .fst (.comp .snd (.pair .snd .fst))) addSigned

theorem subSigned_eval (p q : SignedTy.denote) :
    subSigned.eval (p,q)=encodeInt (integer p-integer q) := by
  change addSigned.eval (p,(q.2,q.1))=_
  rw [addSigned_eval]
  congr 1
  simp only [integer]
  ring

abbrev InterpolateCoordTy := Ty.pair (.pair SignedTy SignedTy) .nat

def interpolateCoordinate (s : Nat) : Code InterpolateCoordTy SignedTy :=
  let p : Code InterpolateCoordTy SignedTy := .comp .fst .fst
  let q : Code InterpolateCoordTy SignedTy := .comp .fst .snd
  let base := .comp (.pair (.const .nat s) p) mulNatSigned
  let delta := .comp (.pair q p) subSigned
  .comp (.pair base (.comp (.pair .snd delta) mulNatSigned)) addSigned

theorem interpolateCoordinate_eval (s t : Nat) (p q : SignedTy.denote) :
    (interpolateCoordinate s).eval ((p,q),t)=
      encodeInt ((s : Int)*integer p+(t : Int)*(integer q-integer p)) := by
  change addSigned.eval (mulNatSigned.eval (s,p),mulNatSigned.eval (t,subSigned.eval (q,p)))=_
  rw [mulNatSigned_eval,subSigned_eval,mulNatSigned_eval,integer_encodeInt,addSigned_eval,
    integer_encodeInt,integer_encodeInt]

def scalePointCode (s : Nat) : Code PointTy PointTy :=
  .pair (.comp (.pair (.const .nat s) .fst) mulNatSigned)
    (.comp (.pair (.const .nat s) .snd) mulNatSigned)

theorem scalePointCode_eval (s : Nat) (p : PointTy.denote) :
    (scalePointCode s).eval p=encodePoint (LatticeSubdivision.scale s (decoded p)) := by
  change (mulNatSigned.eval (s,p.1),mulNatSigned.eval (s,p.2))=_
  rw [mulNatSigned_eval,mulNatSigned_eval]
  rfl

abbrev InterpolateTy := Ty.pair (.pair PointTy PointTy) .nat

def interpolateCode (s : Nat) : Code InterpolateTy PointTy :=
  .pair (.comp (.pair (.pair (.comp .fst (.comp .fst .fst)) (.comp .fst (.comp .snd .fst))) .snd)
    (interpolateCoordinate s))
    (.comp (.pair (.pair (.comp .fst (.comp .fst .snd)) (.comp .fst (.comp .snd .snd))) .snd)
      (interpolateCoordinate s))

theorem interpolateCode_eval (s t : Nat) (p q : PointTy.denote) :
    (interpolateCode s).eval ((p,q),t)=
      encodePoint (LatticeSubdivision.interpolate s (decoded p) (decoded q) t) := by
  change ((interpolateCoordinate s).eval ((p.1,q.1),t),
    (interpolateCoordinate s).eval ((p.2,q.2),t))=_
  rw [interpolateCoordinate_eval,interpolateCoordinate_eval]
  rfl

/-- The scale is fixed when the program is constructed, so this table does
not constitute iteration over a binary input value. -/
def segmentInitCode (s : Nat) : Code (.pair PointTy PointTy) CycleInputTy :=
  .comp (.pair .id (.const (.list .nat) (List.range s))) (.listMapEnv (interpolateCode s))

theorem segmentInitCode_eval (s : Nat) (p q : PointTy.denote) :
    (segmentInitCode s).eval (p,q)=
      (LatticeSubdivision.segmentInit s (decoded p) (decoded q)).map encodePoint := by
  change (List.range s).map (fun t => (interpolateCode s).eval ((p,q),t))=_
  rw [LatticeSubdivision.segmentInit,List.map_map]
  apply List.map_congr_left
  intro t _
  exact interpolateCode_eval s t p q

end GridHardness.LatticeRouteCoreCode
