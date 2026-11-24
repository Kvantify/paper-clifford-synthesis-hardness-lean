/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingTraceCode

/-!
# SAT Clause Inverse Code

Certified inversion of the clause-order permutation by bounded scanning.
The queried height is a binary natural; iteration is over the occurrence list.
-/

@[expose] public section

namespace GridHardness.SatClauseInverseCode
open CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair SatTy .nat

def test : Code (.pair .nat SatCrossingCode.PairTy) .bool :=
  .comp (.pair .fst (.comp .snd .fst)) .natEq

def code : Code InputTy .nat :=
  .comp (.pair .snd (.comp .fst SatClauseOrderCode.indexed))
    (.comp (Code.filterEnv test) (.comp (.listMap .snd) .listSum))

theorem code_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    code.eval (x,(SatClauseOrder.permutation (finiteFormula x) i).val)=i.val := by
  let q := (SatClauseOrder.permutation (finiteFormula x) i).val
  let ys := (SatClauseOrderCode.indexed.eval x).filter (fun r => decide (q=r.1))
  have hn : (SatClauseOrderCode.indexed.eval x).Nodup := by
    apply List.Nodup.of_map (f:=Prod.fst)
    simpa only [SatClauseOrderCode.indexed,Code.eval,List.zipIdx_map_fst] using
      SatClauseOrderCode.permutation_nodup x
  have hp : ys.Perm [(q,i.val)] := by
    apply (List.perm_ext_iff_of_nodup (hn.filter _) (by simp)).mpr
    rintro ⟨v,j⟩
    simp only [ys,List.mem_filter,decide_eq_true_eq,List.mem_singleton,Prod.mk.injEq]
    constructor
    · rintro ⟨hj,hv⟩
      obtain ⟨hj,he⟩ := (SatClauseOrderCode.mem_indexed x v j).mp hj
      have hji : (⟨j,hj⟩ : Fin (3*x.length))=i :=
        (SatClauseOrder.permutation (finiteFormula x)).injective (Fin.ext (he.symm.trans hv.symm))
      exact ⟨hv.symm,congrArg Fin.val hji⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨(SatClauseOrderCode.mem_indexed x q i.val).mpr ⟨i.isLt,rfl⟩,rfl⟩
  change (((Code.filterEnv test).eval (q,SatClauseOrderCode.indexed.eval x)).map Prod.snd).sum=_
  rw [filterEnv_eval]
  change (ys.map Prod.snd).sum=i.val
  simpa using (hp.map Prod.snd).sum_eq

end GridHardness.SatClauseInverseCode
