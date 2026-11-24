/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

/-!
# Grid Embedding

Unary-unary embedding used by the reduction.
Coordinates are first translated into a nonnegative bounding rectangle.
The result preserves the entire Manhattan metric, hence edges and nonedges.
-/

@[expose] public section

namespace CliffordSynthesis.GridEmbedding

/-- A unary unary, including the two boundary cases a=0 and a=n. -/
def unary (n a : Nat) : Fin n → Bool := fun i => decide (i.val < a)

private theorem distance_of_le {n a b : Nat} (hab : a ≤ b) (hb : b ≤ n) :
    hammingDist (unary n a) (unary n b) = b - a := by
  unfold hammingDist
  have hmap : (Finset.univ.filter (fun i : Fin n => unary n a i ≠ unary n b i)).map
      Fin.valEmbedding = Finset.Ico a b := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      change a ≤ i.val ∧ i.val < b
      simp only [unary, ne_eq, decide_eq_decide] at hi
      omega
    · intro hk
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      simp only [unary, ne_eq, decide_eq_decide]
      omega
  rw [← Finset.card_map (f := Fin.valEmbedding), hmap, Nat.card_Ico]

/-- The one-dimensional isometry, without choosing an order on a and b. -/
theorem prefix_distance {n a b : Nat} (ha : a ≤ n) (hb : b ≤ n) :
    hammingDist (unary n a) (unary n b) = (a - b) + (b - a) := by
  rcases le_total a b with hab | hba
  · rw [distance_of_le hab hb, Nat.sub_eq_zero_of_le hab, Nat.zero_add]
  · rw [hammingDist_comm, distance_of_le hba ha, Nat.sub_eq_zero_of_le hba, Nat.add_zero]

/-- Concatenation of the horizontal and vertical unary prefixes. -/
def encode (width height : Nat) (p : Nat × Nat) : Fin width ⊕ Fin height → Bool :=
  Sum.elim (unary width p.1) (unary height p.2)

private theorem hamming_sum {α β : Type*} [Fintype α] [Fintype β]
    (f g : α ⊕ β → Bool) :
    hammingDist f g = hammingDist (f ∘ Sum.inl) (g ∘ Sum.inl) +
      hammingDist (f ∘ Sum.inr) (g ∘ Sum.inr) := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type, Function.comp_def]

/-- Exact Manhattan distance preservation on the bounding rectangle. -/
theorem encode_distance {w h : Nat} {p q : Nat × Nat}
    (hp : p.1 ≤ w ∧ p.2 ≤ h) (hq : q.1 ≤ w ∧ q.2 ≤ h) :
    hammingDist (encode w h p) (encode w h q) =
      (p.1 - q.1) + (q.1 - p.1) + ((p.2 - q.2) + (q.2 - p.2)) := by
  rw [hamming_sum]
  exact congrArg₂ (· + ·) (prefix_distance hp.1 hq.1) (prefix_distance hp.2 hq.2)

/-- Translating the Hamming cube by the start vertex preserves distances. -/
def translate {ι : Type*} (s v : ι → Bool) : ι → Bool := fun i => v i ^^ s i

theorem translate_distance {ι : Type*} [Fintype ι] (s u v : ι → Bool) :
    hammingDist (translate s u) (translate s v) = hammingDist u v := by
  apply hammingDist_comp (fun i a => a ^^ s i)
  intro i a b hab
  cases hs : s i <;> simpa [hs] using hab

theorem translate_start {ι : Type*} (s : ι → Bool) : translate s s = fun _ => false := by
  funext i
  exact Bool.xor_self _

/-- Edges and nonedges are both preserved; there are no spurious cube edges. -/
theorem adjacency_iff {w h : Nat} {p q : Nat × Nat}
    (hp : p.1 ≤ w ∧ p.2 ≤ h) (hq : q.1 ≤ w ∧ q.2 ≤ h)
    (s : Fin w ⊕ Fin h → Bool) :
    hammingDist (translate s (encode w h p)) (translate s (encode w h q)) = 1 ↔
      (p.1 - q.1) + (q.1 - p.1) + ((p.2 - q.2) + (q.2 - p.2)) = 1 := by
  rw [translate_distance, encode_distance hp hq]

theorem encode_injective {w h : Nat} {p q : Nat × Nat}
    (hp : p.1 ≤ w ∧ p.2 ≤ h) (hq : q.1 ≤ w ∧ q.2 ≤ h)
    (he : encode w h p = encode w h q) : p = q := by
  have hd := encode_distance hp hq
  rw [he, hammingDist_self] at hd
  apply Prod.ext <;> omega

end CliffordSynthesis.GridEmbedding
