/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableOrder
public import GridHardness.PositiveSatFinite
import Mathlib.Data.List.GetD

/-!
# SAT Variable Order Finite

The finite formula extracted from a width-three encoded SAT instance
has no unused variable slots except its final total-lookup slot. These
facts depend only on clause widths, not on signs or satisfiability.
-/

@[expose] public section

namespace GridHardness.SatVariableOrder.Finite
open CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def lastSlot (x : SatTy.denote) : Fin ((vsOf x).length+1) :=
  ⟨(vsOf x).length,by omega⟩

/-- Every label in the encoded variable list occurs at an actual one of
the three positions of some clause. -/
theorem label_occurs (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Nat) (ha : a ∈vsOf x) :
    ∃ o : Occurrence x.length, ((x.get o.1).getD o.2.val (0,true)).1=a := by
  have hm := List.mem_map.mp ((mem_vsOf x).mp ha)
  obtain ⟨p,hp,hpa⟩ := hm
  obtain ⟨c,hc,hpc⟩ := List.mem_flatten.mp hp
  obtain ⟨i,hi,hic⟩ := List.getElem_of_mem hc
  obtain ⟨j,hj,hjp⟩ := List.getElem_of_mem hpc
  have hj3 : j<3 := by rw [← hw c hc]; exact hj
  refine ⟨(⟨i,hi⟩,⟨j,hj3⟩),?_⟩
  change (x[i].getD j (0,true)).1=a
  rw [hic,List.getD_eq_getElem _ _ hj,hjp]
  exact hpa

theorem literal_label_mem (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (o : Occurrence x.length) :
    ((x.get o.1).getD o.2.val (0,true)).1∈vsOf x := by
  change (x[o.1.val].getD o.2.val (0,true)).1∈vsOf x
  have hc : x[o.1.val]∈x := List.getElem_mem o.1.isLt
  have hj : o.2.val<x[o.1.val].length := by rw [hw _ hc]; exact o.2.isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact (mem_vsOf x).mpr (List.mem_map.mpr
    ⟨x[o.1.val][o.2.val],List.mem_flatten.mpr
      ⟨x[o.1.val],hc,List.getElem_mem hj⟩,rfl⟩)

/-- Every occurrence belongs to a real variable-list slot, never to the
extra slot that makes arbitrary lookups total. -/
theorem formula_lt_last (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (o : Occurrence x.length) :
    (finiteFormula x o.1 o.2).val<(vsOf x).length := by
  unfold finiteFormula
  rw [varSlot_val_of_mem (literal_label_mem x hw o)]
  exact List.idxOf_lt_length_of_mem (literal_label_mem x hw o)

/-- Every real slot is the value of at least one occurrence. -/
theorem slot_occurs (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Fin ((vsOf x).length +1)) (hv : v.val <(vsOf x).length) :
    ∃ o : Occurrence x.length, finiteFormula x o.1 o.2=v := by
  obtain ⟨o,ho⟩ := label_occurs x hw ((vsOf x)[v.val]) (List.getElem_mem hv)
  refine ⟨o,?_⟩
  apply Fin.ext
  change (varSlot (vsOf x) (((x.get o.1).getD o.2.val (0,true)).1)).val=v.val
  rw [ho,varSlot_val_of_mem (List.getElem_mem hv)]
  exact (nodup_vsOf x).idxOf_getElem v.val hv

theorem count_pos (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Fin ((vsOf x).length +1)) (hv : v.val <(vsOf x).length) :
    0<count (finiteFormula x) v := by
  obtain ⟨o,ho⟩ := slot_occurs x hw v hv
  apply Nat.pos_of_ne_zero
  intro hz
  exact (count_eq_zero_iff (finiteFormula x) v).mp hz o ho

theorem count_last_zero (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    count (finiteFormula x) (lastSlot x)=0 := by
  apply (count_eq_zero_iff (finiteFormula x) (lastSlot x)).mpr
  intro o he
  have h := formula_lt_last x hw o
  rw [he] at h
  exact (Nat.lt_irrefl _ h)

/-- Exactly the final slot is empty, including the empty-formula case. -/
theorem count_zero_iff_last (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Fin ((vsOf x).length +1)) :
    count (finiteFormula x) v=0 ↔ v=lastSlot x := by
  constructor
  · intro hz
    apply Fin.ext
    change v.val=(vsOf x).length
    by_contra hn
    have hv : v.val<(vsOf x).length := by omega
    have hp := count_pos x hw v hv
    omega
  · rintro rfl
    exact count_last_zero x hw

theorem last_prefix (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    SatVariableOrder.prefix (finiteFormula x) (lastSlot x)=3*x.length := by
  have hs := unused_offset (finiteFormula x) (lastSlot x) (count_last_zero x hw)
  exact hs.symm.trans (offset_all (finiteFormula x))

end GridHardness.SatVariableOrder.Finite
