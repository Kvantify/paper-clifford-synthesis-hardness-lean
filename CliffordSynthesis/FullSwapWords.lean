/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FreeSwaps
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Full Swap Words

A short list of transpositions for a finite permutation and the tableau action of
executing the list as free SWAP gates.
-/

public section

namespace CliffordSynthesis.FreeSwaps

variable {n : Nat}

private theorem swapFactorsAux_length {α : Type} [DecidableEq α] (l : List α)
    (p : Equiv.Perm α) (h : ∀ {i}, p i ≠ i → i ∈ l) :
    (Equiv.Perm.swapFactorsAux l p h).val.length ≤ l.length := by
  induction l generalizing p with
  | nil => simp [Equiv.Perm.swapFactorsAux]
  | cons i l ih =>
    simp only [Equiv.Perm.swapFactorsAux]
    split
    · rename_i hi
      have hf : ∀ {x}, p x ≠ x → x ∈ l := fun {x} hx =>
        List.mem_of_ne_of_mem (fun he : x = i => by subst x; exact hx hi.symm) (h hx)
      exact (ih p hf).trans (Nat.le_succ _)
    · have hf : ∀ {x}, (Equiv.swap i (p i) * p) x ≠ x → x ∈ l := fun {_} hx =>
        let he := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hx
        List.mem_of_ne_of_mem he.2 (h he.1)
      exact Nat.succ_le_succ (ih _ hf)

private theorem swap_factors_as_pairs {α : Type} [DecidableEq α] (l : List (Equiv.Perm α))
    (h : ∀ p ∈ l, p.IsSwap) :
    ∃ ss : List (α × α), ss.length = l.length ∧
      ss.map (fun ij => Equiv.swap ij.1 ij.2) = l := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons p l ih =>
    obtain ⟨i, j, _, rfl⟩ := h p (by simp)
    obtain ⟨ss, hl, hm⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact ⟨(i, j) :: ss, by simp [hl], by simp [hm]⟩

/-- A permutation on `n` wires has a transposition word of length at most `n`. -/
theorem short_swap_word (p : Equiv.Perm (Fin n)) :
    ∃ ss : List (Fin n × Fin n), ss.length ≤ n ∧
      (ss.map (fun ij => Equiv.swap ij.1 ij.2)).prod = p := by
  let l := p.swapFactors
  obtain ⟨ss, hlen, he⟩ := swap_factors_as_pairs l.val l.property.2
  refine ⟨ss, ?_, he ▸ l.property.1⟩
  rw [hlen]
  have h := swapFactorsAux_length (Finset.univ.sort : List (Fin n)) p
    (fun {_} _ => (Finset.mem_sort _).mpr (Finset.mem_univ _))
  simpa [l, Equiv.Perm.swapFactors] using h

theorem execute_swap_word (ss : List (Fin n × Fin n)) (a : Circuit.Tableau n) :
    execute (ss.map (fun ij => Step.swap ij.1 ij.2)) a =
      reorder (ss.map (fun ij => Equiv.swap ij.1 ij.2)).prod a := by
  induction ss generalizing a with
  | nil => exact (reorder_one a).symm
  | cons ij ss ih =>
    simp only [List.map_cons, execute, List.prod_cons, ih, reorder_reorder]
    rfl

end CliffordSynthesis.FreeSwaps
