/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalHorizontal
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Corrected SAT Interval Numbering

Reuse the eight old XOR names for the refreshed section zero and append
exactly forty fresh names. This identifies vertices of the actual refinement,
rather than merely comparing cardinalities. The ambient equivalence uses a
classical inverse; its forward map and all integer-name equations are explicit.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.Numbering
open XorLineRegistry XorLineSchedule XorLine

section Old
variable {V : Type*} (e : Fin 8 → V)

def oldEquiv : Marked.Outside (sourceMarker (n := 4) e) ≃
    {v : V // v ∉ Set.range e} where
  toFun := fun o => by
    rcases o with ⟨v,hv⟩
    cases v with
    | inl v =>
      exact ⟨v, by
        rintro ⟨k,hk⟩
        exact hv ⟨.inl k, congrArg Sum.inl hk⟩⟩
    | inr p => exact False.elim (hv ⟨.inr p,rfl⟩)
  invFun := fun v => ⟨.inl v.val,
    Bundle.old_not_in_sourceMarker e v.val (fun k hk => v.property ⟨k,hk⟩)⟩
  left_inv := by
    rintro ⟨v,hv⟩
    cases v with
    | inl v => rfl
    | inr p => exact False.elim (hv ⟨.inr p,rfl⟩)
  right_inv := fun _ => rfl

def restore : ({v : V // v ∉ Set.range e} ⊕ Fin 8) → V
  | .inl v => v.val
  | .inr k => e k

theorem restore_bijective (he : Function.Injective e) : Function.Bijective (restore e) := by
  constructor
  · rintro (u | i) (v | j) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact False.elim (u.property ⟨j,h.symm⟩)
    · exact False.elim (v.property ⟨i,h⟩)
    · exact congrArg Sum.inr (he h)
  · intro v
    classical
    by_cases hv : v ∈ Set.range e
    · obtain ⟨k,rfl⟩ := hv
      exact ⟨.inr k,rfl⟩
    · exact ⟨.inl ⟨v,hv⟩,rfl⟩

noncomputable def restoreEquiv (he : Function.Injective e) :
    ({v : V // v ∉ Set.range e} ⊕ Fin 8) ≃ V :=
  Equiv.ofBijective (restore e) (restore_bijective e he)

end Old

def tileNames : XorLine.Vertex 4 → Fin 8 ⊕ SatCrossingHorizontal.RetainedVertex
  | .inl (i,j) => if hi : i=0 then .inl j else .inr ⟨.inl (i,j),hi⟩
  | .inr p => .inr ⟨.inr p,trivial⟩

def tileOriginal : Fin 8 ⊕ SatCrossingHorizontal.RetainedVertex → XorLine.Vertex 4
  | .inl j => x 0 j
  | .inr v => v.val

def tileEquiv : XorLine.Vertex 4 ≃ Fin 8 ⊕ SatCrossingHorizontal.RetainedVertex where
  toFun := tileNames
  invFun := tileOriginal
  left_inv := by
    rintro (⟨i,j⟩ | p)
    · by_cases hi : i=0
      · subst i
        rfl
      · simp [tileNames,tileOriginal,hi]
    · rfl
  right_inv := by
    rintro (j | ⟨v,hv⟩)
    · rfl
    · rcases v with ⟨i,j⟩ | p
      · simp only [SatCrossingHorizontal.Retained] at hv
        simp [tileOriginal,tileNames,hv]
      · rfl

@[simp] theorem tileEquiv_active (j : Fin 8) : tileEquiv (x 0 j) = .inl j := rfl

@[simp] theorem tileEquiv_retained (v : SatCrossingHorizontal.RetainedVertex) :
    tileEquiv v.val = .inr v := by
  obtain ⟨v,hv⟩ := v
  rcases v with ⟨i,j⟩ | p
  · simp only [SatCrossingHorizontal.Retained] at hv
    simp [tileEquiv,tileNames,hv]
  · rfl

section Crossing
variable {n : Nat} (s : IntervalState n) (a : Fin n) (line height : Nat)
variable (hc : s.Covered line height)

/-- Concrete vertex correspondence: section zero uses the old active XOR
names, all surviving vertices keep their names, and forty vertices are new. -/
noncomputable def equiv : (s.cross a line height hc).Vertex ≃
    s.Vertex ⊕ SatCrossingHorizontal.RetainedVertex :=
  (Equiv.sumCongr (oldEquiv (s.positioned.registry.xors.embed a)) tileEquiv).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
      (Equiv.sumCongr (restoreEquiv (s.positioned.registry.xors.embed a)
        (s.positioned.registry.xors.embed_injective a)) (Equiv.refl _)))

theorem equiv_survivor (v : s.Vertex)
    (hv : ∀ k, s.positioned.registry.xors.embed a k ≠ v) :
    equiv s a line height hc (.inl ⟨.inl v,Bundle.old_not_in_sourceMarker _ _ hv⟩) =
      .inl v := rfl

theorem equiv_active (j : Fin 8) :
    equiv s a line height hc (.inr (x 0 j)) =
      .inl (s.positioned.registry.xors.embed a j) := rfl

theorem equiv_retained (v : SatCrossingHorizontal.RetainedVertex) :
    equiv s a line height hc (.inr v.val) = .inr v := by
  change (Equiv.sumCongr (restoreEquiv (s.positioned.registry.xors.embed a)
    (s.positioned.registry.xors.embed_injective a)) (Equiv.refl _))
    ((Equiv.sumAssoc _ _ _).symm (Sum.inr (tileEquiv v.val))) = _
  rw [tileEquiv_retained]
  rfl

theorem equiv_current_xor (j : Fin 8) :
    equiv s a line height hc ((s.cross a line height hc).positioned.registry.xors.embed a j) =
      .inl (s.positioned.registry.xors.embed a j) := by
  rw [Horizontal.latest_active]
  exact equiv_active s a line height hc j

theorem equiv_other_xor (b : Fin n) (hba : b ≠a) (j : Fin 8) :
    equiv s a line height hc ((s.cross a line height hc).positioned.registry.xors.embed b j) =
      .inl (s.positioned.registry.xors.embed b j) := by
  change equiv s a line height hc
    (s.positioned.registry.crossXor a (s.select line height hc).val b j) = _
  rw [Registry.crossXor_other _ _ _ _ hba]
  rfl

end Crossing

/-- Sections one through four use names 0--31; the eight row vertices use
32--39. Thus the forty fresh names do not depend on the ambient graph. -/
def retainedIndex (v : SatCrossingHorizontal.RetainedVertex) : Fin 40 :=
  match v with
  | ⟨.inl (i,j),hi⟩ => ⟨8*(i.val-1)+j.val,by
      have hilt := i.isLt
      have hjlt := j.isLt
      have hinz : i.val≠0 := fun h => hi (Fin.ext h)
      omega⟩
  | ⟨.inr (i,b),_⟩ => ⟨32+2*i.val+(if b then 1 else 0),by
      have hi := i.isLt
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

theorem retainedIndex_bijective : Function.Bijective retainedIndex := by decide +kernel

noncomputable def retainedEquiv : SatCrossingHorizontal.RetainedVertex ≃ Fin 40 :=
  Equiv.ofBijective retainedIndex retainedIndex_bijective

section Numbered
variable {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
variable (a : Fin n) (line height : Nat) (hc : s.Covered line height)

noncomputable def finEquiv : (s.cross a line height hc).Vertex ≃ Fin (N+40) :=
  (equiv s a line height hc).trans
    ((Equiv.sumCongr number retainedEquiv).trans finSumFinEquiv)

theorem finEquiv_survivor (v : s.Vertex)
    (hv : ∀ k, s.positioned.registry.xors.embed a k ≠ v) :
    (finEquiv s number a line height hc
      (.inl ⟨.inl v,Bundle.old_not_in_sourceMarker _ _ hv⟩)).val = (number v).val := rfl

theorem finEquiv_current_xor (j : Fin 8) :
    (finEquiv s number a line height hc
      ((s.cross a line height hc).positioned.registry.xors.embed a j)).val =
      (number (s.positioned.registry.xors.embed a j)).val := by
  change (finSumFinEquiv ((Equiv.sumCongr number retainedEquiv)
    (equiv s a line height hc _))).val = _
  rw [equiv_current_xor]
  rfl

theorem finEquiv_retained (v : SatCrossingHorizontal.RetainedVertex) :
    (finEquiv s number a line height hc (.inr v.val)).val = N+(retainedIndex v).val := by
  change (finSumFinEquiv ((Equiv.sumCongr number retainedEquiv)
    (equiv s a line height hc _))).val = _
  rw [equiv_retained]
  rfl

end Numbered
end GridHardness.CorrectedSatInterval.Numbering
