/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRun
public import GridHardness.SatCrossingCode

/-!
# Corrected SAT Interval Catalogue

The two-sided sweep executes precisely the geometric inversion catalogue,
once per crossing. Its height function is the actual occurrence permutation.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval

def trace (height : Nat → Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | n+1, j => (requests height j).map (fun i => (i,j)) ++ trace height n (j+1)

theorem trace_length (height : Nat → Nat) (n : Nat) :
    ∀ j, (trace height n j).length = moveCount height n j := by
  induction n with
  | zero => intro j; rfl
  | succ n ih => intro j; simp only [trace, List.length_append, List.length_map, moveCount, ih]

theorem mem_trace (height : Nat → Nat) (n : Nat) : ∀ j (p : Nat × Nat),
    p ∈ trace height n j ↔
      p.1 < p.2 ∧ height p.2 < height p.1 ∧ j ≤ p.2 ∧ p.2 < j+n := by
  induction n with
  | zero => intro j p; simp only [trace, List.not_mem_nil, false_iff]; omega
  | succ n ih =>
    intro j p
    have hhead : p ∈ (requests height j).map (fun i => (i,j)) ↔
        p.1 < j ∧ height j < height p.1 ∧ p.2 = j := by
      constructor
      · intro hp
        obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
        obtain ⟨hij, hheight⟩ := (mem_requests height i j).mp hi
        cases he
        exact ⟨hij, hheight, rfl⟩
      · rintro ⟨hi, hh, he⟩
        apply List.mem_map.mpr
        exact ⟨p.1, (mem_requests height p.1 j).mpr ⟨hi,hh⟩, Prod.ext rfl he.symm⟩
    rw [trace, List.mem_append, hhead, ih]
    constructor
    · rintro (⟨hi, hh, he⟩ | ⟨hi, hh, hj, hk⟩)
      · exact ⟨by omega, by simpa [he] using hh, by omega, by omega⟩
      · exact ⟨hi, hh, by omega, by omega⟩
    · rintro ⟨hi, hh, hj, hk⟩
      by_cases he : p.2 = j
      · exact Or.inl ⟨by omega, by simpa [he] using hh, he⟩
      · exact Or.inr ⟨hi, hh, by omega, by omega⟩

theorem trace_nodup (height : Nat → Nat) (n : Nat) :
    ∀ j, (trace height n j).Nodup := by
  induction n with
  | zero => intro j; simp [trace]
  | succ n ih =>
    intro j
    rw [trace, List.nodup_append]
    refine ⟨List.Nodup.map_on (fun i _ k _ he => (Prod.mk.inj he).1)
      (requests_nodup height j), ih (j+1), ?_⟩
    intro p hp q hq he
    obtain ⟨i, hi, hpi⟩ := List.mem_map.mp hp
    have hq' := (mem_trace height n (j+1) q).mp hq
    have hsecond : q.2 = j := by rw [← he, ← hpi]
    omega

/-- Extend a finite permutation by the identity, and shift its values by one
to leave zero as the common lower endpoint of the vertical intervals. -/
def permutationHeight {N : Nat} (p : Equiv.Perm (Fin N)) (i : Nat) : Nat :=
  if hi : i < N then (p ⟨i,hi⟩).val + 1 else i+1

theorem permutationHeight_apply {N : Nat} (p : Equiv.Perm (Fin N)) (i : Fin N) :
    permutationHeight p i.val = (p i).val+1 := by
  simp [permutationHeight, i.isLt]

theorem permutationHeight_pos {N : Nat} (p : Equiv.Perm (Fin N)) (i : Nat) :
    0 < permutationHeight p i := by
  unfold permutationHeight
  split <;> omega

theorem permutationHeight_injective {N : Nat} (p : Equiv.Perm (Fin N)) :
    Function.Injective (permutationHeight p) := by
  intro i j he
  unfold permutationHeight at he
  split at he <;> split at he
  · rename_i hi hj
    have hp : p ⟨i,hi⟩ = p ⟨j,hj⟩ := Fin.ext (by omega)
    exact congrArg Fin.val (p.injective hp)
  · rename_i hi hj
    have hb := (p ⟨i,hi⟩).isLt
    omega
  · rename_i hi hj
    have hb := (p ⟨j,hj⟩).isLt
    omega
  · omega

def formulaHeight {n m : Nat} (φ : PlanarSatAssembly.Formula n m) : Nat → Nat :=
  permutationHeight (SatWireLayout.permutation φ)

theorem formulaHeight_injective {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    Function.Injective (formulaHeight φ) := permutationHeight_injective _

theorem formulaHeight_pos {n m : Nat} (φ : PlanarSatAssembly.Formula n m) (i : Nat) :
    0 < formulaHeight φ i := permutationHeight_pos _ _

theorem covers_inversion {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (i j : Fin (3 *m)) :
    (i.val,j.val) ∈ trace (formulaHeight φ) (3*m) 0 ↔
      i<j ∧ SatWireLayout.permutation φ j < SatWireLayout.permutation φ i := by
  rw [mem_trace]
  simp only [formulaHeight, permutationHeight_apply]
  have hj := j.isLt
  simp only [Nat.zero_le, Nat.zero_add, true_and]
  constructor
  · intro h
    exact ⟨h.1, by simpa using h.2.1⟩
  · intro h
    exact ⟨h.1, by simpa using h.2, hj⟩

theorem covers_catalogue (x : CliffordComplexity.SatTy.denote) (p : Nat × Nat) :
    p ∈ trace (formulaHeight (finiteFormula x)) (3*x.length) 0 ↔
      p ∈ SatCrossingCode.crossings.eval x := by
  constructor
  · intro hp
    have h := (mem_trace _ _ _ p).mp hp
    have hi : p.1 < 3*x.length := by omega
    have hj : p.2 < 3*x.length := by omega
    exact (SatCrossingCode.crossing_cell_iff x ⟨p.1,hi⟩ ⟨p.2,hj⟩).mpr
      ((covers_inversion _ ⟨p.1,hi⟩ ⟨p.2,hj⟩).mp hp)
  · intro hp
    obtain ⟨hi,hj,_,_⟩ := (SatCrossingCode.mem_crossings x p.1 p.2).mp hp
    exact (covers_inversion _ ⟨p.1,hi⟩ ⟨p.2,hj⟩).mpr
      ((SatCrossingCode.crossing_cell_iff x ⟨p.1,hi⟩ ⟨p.2,hj⟩).mp hp)

theorem trace_perm_catalogue (x : CliffordComplexity.SatTy.denote) :
    (trace (formulaHeight (finiteFormula x)) (3*x.length) 0).Perm
      (SatCrossingCode.crossings.eval x) :=
  (List.perm_ext_iff_of_nodup (trace_nodup _ _ _) (SatCrossingCode.crossings_nodup x)).mpr
    (covers_catalogue x)

theorem actual_move_count (x : CliffordComplexity.SatTy.denote) :
    moveCount (formulaHeight (finiteFormula x)) (3*x.length) 0 =
      (SatCrossingCode.crossings.eval x).length := by
  rw [← trace_length]
  exact (trace_perm_catalogue x).length_eq

end GridHardness.CorrectedSatInterval
