/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetirementPathCode

/-!
# SAT Residual Path Code

Certified upper and lower residual slices of the complete retirement
path. Slice lengths are bounded by the already proved complete-path bound.
-/

@[expose] public section

namespace GridHardness.SatResidualPathCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open SatCrossingRetirement SatRetirementGeometryCode SatConnectorRouteCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000
attribute [local irreducible] SatCrossingTraceCode.rankValue

abbrev CellTy := Ty.pair SatTy SatCrossingCode.PairTy
abbrev SliceTy := Ty.pair RowTy (.pair .nat .nat)

def indices : Code SliceTy (.list .nat) :=
  .comp (.pair (.comp (.comp .fst .fst) (SatAffineRangeCode.padding 6144 2048)) (.comp .snd .snd))
    (BoundedRangeCode.code .nat)

def localSlice (r : Fin 4) : Code SliceTy CycleInputTy :=
  .comp (.pair (.pair (.comp .fst SatRetirementPathCode.params) (.comp .snd .fst)) indices)
    (.listMapEnv (.comp (.pair (.comp .fst .fst) (Code.add (.comp .fst .snd) .snd))
      (SatRetirementPathCode.pathPointCode r)))

def slice (r : Fin 4) : Code SliceTy CycleInputTy :=
  .comp (.pair (.comp .fst SatRetirementPathCode.frameCode) (localSlice r))
    (.listMapEnv GridFrameCode.point)

theorem slice_eval (x : SatTy.denote) (i : Fin (3 *x.length)) (r : Fin 4) (k n : Nat)
    (hn : n ≤6144 *x.length +2048) :
    (slice r).eval ((x,i.val),(k,n))=
      (((List.range n).map (fun a => pathPoint (Placement.span (Residual.rowEnd (perm x) i) i)
        (Placement.height (perm x) i) r (k+a))).map
          (Placement.frame (Residual.rowEnd (perm x) i) i).map).map encodePoint := by
  have hi : indices.eval ((x,i.val),(k,n))=List.range n := by
    apply BoundedRangeCode.code_eval_of_le
    change n≤((SatAffineRangeCode.padding 6144 2048).eval x).length
    rwa [SatAffineRangeCode.padding_length]
  have hl : (localSlice r).eval ((x,i.val),(k,n))=
      ((List.range n).map (fun a => pathPoint (Placement.span (Residual.rowEnd (perm x) i) i)
        (Placement.height (perm x) i) r (k+a))).map encodePoint := by
    change (indices.eval ((x,i.val),(k,n))).map (fun a => (SatRetirementPathCode.pathPointCode r).eval
      (SatRetirementPathCode.params.eval (x,i.val),k+a))=_
    rw [hi,SatRetirementPathCode.params_eval,List.map_map]
    exact List.map_congr_left (fun a _ => SatRetirementPathCode.pathPointCode_eval _ _ _ _ r)
  change ((localSlice r).eval ((x,i.val),(k,n))).map
    (fun q => GridFrameCode.point.eval (SatRetirementPathCode.frameCode.eval (x,i.val),q))=_
  rw [hl,SatRetirementPathCode.frameCode_eval]
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]

def firstRow : Code CellTy RowTy := .pair .fst (.comp .snd .fst)
def secondRow : Code CellTy RowTy := .pair .fst (.comp .snd .snd)

def cutArithmetic (r : Fin 4) (b : Bool) : Code SatRetirementPathCode.ParamsTy .nat :=
  .comp (minus (plus (natSigned (Code.add .fst (.comp .snd .fst)))
    (.const SignedTy (encodeInt (offset r))))
    (plus (natSigned (.comp .snd .snd)) (.const SignedTy (encodeInt (if b then 10 else -10))))) .fst

theorem cutArithmetic_eval (t h l : Nat) (r : Fin 4) (b : Bool) :
    (cutArithmetic r b).eval (t,h,l)=((t:Int)+h+offset r-((l:Int)+(if b then 10 else -10))).toNat := by
  simp only [cutArithmetic,Code.eval,minus_eval,plus_eval,natSigned_eval,integer_encodeInt]
  change (((t+h:Nat):Int)+offset r-((l:Int)+(if b then 10 else -10))).toNat=_
  push_cast
  rfl

def cutCode (r : Fin 4) (b : Bool) : Code CellTy .nat :=
  .comp (.pair (.comp firstRow (.comp SatRetirementPathCode.params (SatRetirementPathCode.turnCode r)))
    (.pair (.comp firstRow highNat) (.comp secondRow highNat))) (cutArithmetic r b)

theorem highNat_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    (highNat.eval (x,j.val):Int)=512*PermutationWireLayout.high (perm x) j := by
  have he : highNat.eval (x,j.val)=512*(3*x.length+2+(perm x j).val) := by
    change 512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,j.val))=_
    rw [SatCrossingTraceCode.rankValue_eval]
  rw [he]; rfl

theorem cutCode_eval (x : SatTy.denote) (i j : Fin (3 *x.length)) (r : Fin 4) (b : Bool) :
    (cutCode r b).eval (x,(i.val,j.val))=
      Segments.cut (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
        r (Segments.cutHeight (perm x) i j b) := by
  change (cutArithmetic r b).eval ((SatRetirementPathCode.turnCode r).eval
    (SatRetirementPathCode.params.eval (x,i.val)),highNat.eval (x,i.val),highNat.eval (x,j.val))=_
  rw [cutArithmetic_eval,SatRetirementPathCode.params_eval,highNat_eval,highNat_eval]
  change ((turn (Placement.span (Residual.rowEnd (perm x) i) i) r:Int)+
    512*PermutationWireLayout.high (perm x) i+offset r-
    (512*PermutationWireLayout.high (perm x) j+(if b then 10 else -10))).toNat=_
  unfold Segments.cut Segments.cutHeight
  have hp := Placement.parameters (perm x) (Residual.rowEnd (perm x) i) i (Catalogue.last_before _ _)
  congr 1
  omega

def lengthCode (r : Fin 4) (b : Bool) : Code CellTy .nat :=
  if b then Code.add (cutCode r true) (.const .nat 1)
  else .comp (.pair (.comp firstRow (.comp SatRetirementPathCode.params SatRetirementPathCode.lengthCode))
    (cutCode r false)) .natSub

def orient (r : Fin 4) : Code CycleInputTy CycleInputTy :=
  if r.val%2=0 then .id else LatticeRouteCoreCode.reverseCode PointTy

theorem orient_eval (r : Fin 4) (xs : CycleInputTy.denote) :
    (orient r).eval xs=if r.val%2=0 then xs else xs.reverse := by
  unfold orient
  split_ifs <;> simp only [Code.eval,LatticeRouteCoreCode.reverseCode_eval]

def code (r : Fin 4) (b : Bool) : Code CellTy CycleInputTy :=
  .comp (.pair firstRow (.pair (if b then .const .nat 0 else cutCode r false) (lengthCode r b)))
    (.comp (slice r) (orient r))

theorem whole_bound (x : SatTy.denote) (i : Fin (3 *x.length)) (r : Fin 4) :
    Placement.span (Residual.rowEnd (perm x) i) i+Placement.height (perm x) i+Placement.tail i+47≤
      6144*x.length+2048 := by
  have hb := Placement.route_length_bound (perm x) (Residual.rowEnd (perm x) i) i (Catalogue.last_before _ _) r
  rw [Placement.route,List.length_map,SatCrossingRetirement.route_length] at hb
  omega

theorem upperSlice_eval (x : SatTy.denote) (i j : Fin (3 *x.length))
    (hij : SatCrossingRouting.Active (perm x) i j) (r : Fin 4) :
    (slice r).eval ((x,i.val),(0,(cutCode r true).eval (x,(i.val,j.val))+1))=
      ((Segments.headPath (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
        r (Segments.cutHeight (perm x) i j true)).map
          (Placement.frame (Residual.rowEnd (perm x) i) i).map).map encodePoint := by
  have hp := Placement.parameters (perm x) (Residual.rowEnd (perm x) i) i (Catalogue.last_before _ _)
  have ht := turn_bounds (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.tail i) hp.2.1 r
  have hb := whole_bound x i r
  have hc := Segments.cut_bounds (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
    r (Segments.cutHeight (perm x) i j true) (Segments.cutHeight_bounds (perm x) i j hij r true)
  rw [cutCode_eval,slice_eval x i r _ _ (by dsimp [finish] at ht; omega)]
  simp only [Nat.zero_add,Segments.headPath]

theorem lowerLength_eval (x : SatTy.denote) (i j : Fin (3 *x.length))
    (hij : SatCrossingRouting.Active (perm x) i j) (r : Fin 4) :
    (lengthCode r false).eval (x,(i.val,j.val))=
      finish (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.tail i)+Placement.height (perm x) i-
        Segments.cut (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
          r (Segments.cutHeight (perm x) i j false)+1 := by
  have hp := Placement.parameters (perm x) (Residual.rowEnd (perm x) i) i (Catalogue.last_before _ _)
  have ht := turn_bounds (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.tail i) hp.2.1 r
  have hc := Segments.cut_bounds (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
    r (Segments.cutHeight (perm x) i j false) (Segments.cutHeight_bounds (perm x) i j hij r false)
  change SatRetirementPathCode.lengthCode.eval (SatRetirementPathCode.params.eval (x,i.val))-
    (cutCode r false).eval (x,(i.val,j.val))=_
  rw [SatRetirementPathCode.params_eval,cutCode_eval]
  change Placement.span (Residual.rowEnd (perm x) i) i+Placement.height (perm x) i+Placement.tail i+47-_=_
  dsimp [finish] at ht ⊢
  omega

theorem lowerSlice_eval (x : SatTy.denote) (i j : Fin (3 *x.length))
    (hij : SatCrossingRouting.Active (perm x) i j) (r : Fin 4) :
    (slice r).eval ((x,i.val),((cutCode r false).eval (x,(i.val,j.val)),(lengthCode r false).eval (x,(i.val,j.val))))=
      ((Segments.tailPath (Placement.span (Residual.rowEnd (perm x) i) i) (Placement.height (perm x) i)
        (Placement.tail i) r (Segments.cutHeight (perm x) i j false)).map
          (Placement.frame (Residual.rowEnd (perm x) i) i).map).map encodePoint := by
  have hb := whole_bound x i r
  rw [cutCode_eval,lowerLength_eval x i j hij r]
  rw [slice_eval x i r _ _ (by dsimp [finish]; omega)]
  simp only [Segments.tailPath,Nat.add_comm]

theorem code_eval (x : SatTy.denote) (i j : Fin (3 *x.length)) (hij : SatCrossingRouting.Active (perm x) i j)
    (r : Fin 4) (b : Bool) : (code r b).eval (x,(i.val,j.val))=
      (if b then Segments.upper (perm x) (Residual.rowEnd (perm x) i) i j r
       else Segments.lower (perm x) (Residual.rowEnd (perm x) i) i j r).map encodePoint := by
  cases b
  · change (orient r).eval ((slice r).eval ((x,i.val),
      ((cutCode r false).eval (x,(i.val,j.val)),(lengthCode r false).eval (x,(i.val,j.val)))))=_
    rw [orient_eval,lowerSlice_eval x i j hij r]
    by_cases hr : r.val%2=0 <;> simp only [Bool.false_eq_true,hr,ite_true,ite_false,Segments.lower,List.map_reverse]
  · change (orient r).eval ((slice r).eval ((x,i.val),
      (0,(cutCode r true).eval (x,(i.val,j.val))+1)))=_
    rw [orient_eval,upperSlice_eval x i j hij r]
    by_cases hr : r.val%2=0 <;> simp only [hr,ite_true,ite_false,Segments.upper,List.map_reverse]

end GridHardness.SatResidualPathCode
