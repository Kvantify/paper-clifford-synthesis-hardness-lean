/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetirementGeometryCode
public import GridHardness.SatConnectorRouteCode
public import GridHardness.SatAffineRangeCode
public import GridHardness.BoundedRangeCode

/-!
# SAT Retirement Path Code

The complete three-segment retirement path is sampled by a certified
list program. Its loop fuel is linear in the explicit SAT clause list.
-/

@[expose] public section

namespace GridHardness.SatRetirementPathCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open SatCrossingRetirement SatRetirementGeometryCode SatConnectorRouteCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000
attribute [local irreducible] SatCrossingTraceCode.rankValue leftNat

abbrev ParamsTy := Ty.pair .nat (.pair .nat .nat)
abbrev SampleTy := Ty.pair ParamsTy .nat

def turnCode (r : Fin 4) : Code ParamsTy .nat :=
  .comp (.pair (Code.add .fst (.const .nat 45)) (.const .nat (30*r.val))) .natSub

def pathPointCode (r : Fin 4) : Code SampleTy PointTy :=
  let turn : Code SampleTy .nat := .comp .fst (turnCode r)
  let height : Code SampleTy .nat := .comp .fst (.comp .snd .fst)
  let upper : Code SampleTy SignedTy := plus (natSigned height) (.const SignedTy (encodeInt (offset r)))
  .branch (.comp (.pair .snd turn) .natLe)
    (.pair (natSigned .snd) upper)
    (.branch (.comp (.pair .snd (Code.add turn height)) .natLe)
      (.pair (natSigned turn) (minus upper (minus (natSigned .snd) (natSigned turn))))
      (.pair (minus (natSigned .snd) (natSigned height)) (.const SignedTy (encodeInt (offset r)))))

theorem pathPointCode_eval (s h t k : Nat) (r : Fin 4) :
    (pathPointCode r).eval ((s,h,t),k)=encodePoint (pathPoint s h r k) := by
  by_cases hk : k≤turn s r <;> by_cases hkh : k≤turn s r+h
  all_goals dsimp only [turn] at hk hkh
  all_goals
    simp [pathPointCode,turnCode,Code.add,Code.eval,plus_eval,minus_eval,natSigned_eval,
      encodePoint,integer_encodeInt,pathPoint,turn,hk,hkh]
    <;> congr 1 <;> omega

def spanCode : Code RowTy .nat := .comp (.pair lowNat leftNat) .natSub
def heightCode : Code RowTy .nat := .comp (.pair highNat lowNat) .natSub
def tailCode : Code RowTy .nat :=
  .comp (.pair rightNat (Code.add lowNat (.const .nat 46))) .natSub

def params : Code RowTy ParamsTy := .pair spanCode (.pair heightCode tailCode)

theorem params_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    params.eval (x,i.val)=(Placement.span (Residual.rowEnd (perm x) i) i,
      Placement.height (perm x) i,Placement.tail i) := by
  have hp := Placement.parameters (perm x) (Residual.rowEnd (perm x) i) i (Catalogue.last_before _ _)
  have hl := leftNat_eval x i
  have hh : highNat.eval (x,i.val)=512*(3*x.length+2+(perm x i).val) := by
    change 512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,i.val))=_
    rw [SatCrossingTraceCode.rankValue_eval]
  change (lowNat.eval (x,i.val)-leftNat.eval (x,i.val),
    highNat.eval (x,i.val)-lowNat.eval (x,i.val),
    rightNat.eval (x,i.val)-(lowNat.eval (x,i.val)+46))=_
  rw [hh]
  change (512*(i.val+1)-leftNat.eval (x,i.val),
    512*(3*x.length+2+(perm x i).val)-512*(i.val+1),
    512*(3*x.length+1)+65-(512*(i.val+1)+46))=_
  dsimp [PermutationWireLayout.low,PermutationWireLayout.high] at hp
  apply Prod.ext
  · dsimp; omega
  · apply Prod.ext <;> dsimp <;> omega

def frameCode : Code RowTy FrameTy :=
  .pair (.const .bool true) (.pair (.const .bool false) (.pair (.const .bool false)
    (.pair (natSigned leftNat) (natSigned lowNat))))

theorem frameCode_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    frameCode.eval (x,i.val)=encodeFrame (Placement.frame (Residual.rowEnd (perm x) i) i) := by
  change (true,false,false,(natSigned leftNat).eval (x,i.val),(natSigned lowNat).eval (x,i.val))=_
  rw [natSigned_eval,natSigned_eval,leftNat_eval]
  rfl

def lengthCode : Code ParamsTy .nat :=
  Code.add (Code.add (Code.add .fst (.comp .snd .fst)) (.comp .snd .snd)) (.const .nat 47)

def indices : Code RowTy (.list .nat) :=
  .comp (.pair (.comp .fst (SatAffineRangeCode.padding 6144 2048)) (.comp params lengthCode))
    (BoundedRangeCode.code .nat)

theorem indices_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    indices.eval (x,i.val)=List.range (Placement.span (Residual.rowEnd (perm x) i) i+
      Placement.height (perm x) i+Placement.tail i+47) := by
  change (BoundedRangeCode.code .nat).eval ((SatAffineRangeCode.padding 6144 2048).eval x,
    lengthCode.eval (params.eval (x,i.val)))=_
  rw [params_eval]
  apply BoundedRangeCode.code_eval_of_le
  rw [SatAffineRangeCode.padding_length]
  change Placement.span (Residual.rowEnd (perm x) i) i+Placement.height (perm x) i+Placement.tail i+47≤_
  have hb := Placement.route_length_bound (perm x) (Residual.rowEnd (perm x) i) i
    (Catalogue.last_before _ _) (0 : Fin 4)
  rw [Placement.route,List.length_map,SatCrossingRetirement.route_length] at hb
  omega

def localPath (r : Fin 4) : Code RowTy CycleInputTy :=
  .comp (.pair params indices) (.listMapEnv (pathPointCode r))

def path (r : Fin 4) : Code RowTy CycleInputTy :=
  .comp (.pair frameCode (localPath r)) (.listMapEnv GridFrameCode.point)

theorem localPath_eval (x : SatTy.denote) (i : Fin (3 *x.length)) (r : Fin 4) :
    (localPath r).eval (x,i.val)=(SatCrossingRetirement.path
      (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
        (Placement.tail i) r).map encodePoint := by
  change (indices.eval (x,i.val)).map (fun k => (pathPointCode r).eval (params.eval (x,i.val),k))=_
  rw [indices_eval,params_eval]
  unfold SatCrossingRetirement.path
  rw [List.map_map]
  have he : Placement.span (Residual.rowEnd (perm x) i) i+Placement.height (perm x) i+Placement.tail i+47=
      finish (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.tail i)+Placement.height (perm x) i+1 := by
    unfold finish; omega
  rw [he]
  exact List.map_congr_left (fun k _ => pathPointCode_eval _ _ _ k r)

theorem path_eval (x : SatTy.denote) (i : Fin (3 *x.length)) (r : Fin 4) :
    (path r).eval (x,i.val)=((SatCrossingRetirement.path
      (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
        (Placement.tail i) r).map (Placement.frame (Residual.rowEnd (perm x) i) i).map).map encodePoint := by
  change ((localPath r).eval (x,i.val)).map (fun q => GridFrameCode.point.eval (frameCode.eval (x,i.val),q))=_
  rw [localPath_eval,frameCode_eval,List.map_map,List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]

def route (r : Fin 4) : Code RowTy CycleInputTy :=
  .comp (path r) (if r.val%2=0 then .id else LatticeRouteCoreCode.reverseCode PointTy)

theorem route_eval (x : SatTy.denote) (i : Fin (3 *x.length)) (r : Fin 4) :
    (route r).eval (x,i.val)=(Placement.route (perm x) (Residual.rowEnd (perm x) i) i r).map encodePoint := by
  unfold route
  by_cases hr : r.val%2=0
  · simp only [hr,ite_true,Code.eval]
    rw [path_eval]
    simp only [Placement.route,SatCrossingRetirement.route,hr,ite_true]
  · simp only [hr,ite_false,Code.eval]
    rw [LatticeRouteCoreCode.reverseCode_eval,path_eval]
    simp only [Placement.route,SatCrossingRetirement.route,hr,ite_false,List.map_reverse]

end GridHardness.SatRetirementPathCode
