/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatXorInterface
public import GridHardness.XorWireNetwork
public import GridHardness.PlanarSatReduction
public import GridHardness.HamiltonianRelabel

/-!
# SAT Wire Expansion

Stretch every occurrence XOR in the actual SAT construction. The new
graph and all of its connections are independent of any satisfying assignment.
-/

@[expose] public section

namespace GridHardness.SatWireExpansion
open PlanarSatAssembly

abbrev ExpandedVertex (n m k : Nat) := Outside n m ⊕ (Occurrence m × XorWire.Vertex k)

def entryIndex (s : Bool) : Fin 8 := if s then 3 else 4
def exitIndex (s : Bool) : Fin 8 := if s then 0 else 7

def outside {n m : Nat} (φ : Formula n m) (a b : Outside n m) : Prop :=
  Adj φ (outsideVertex a) (outsideVertex b)
def enter {n m : Nat} (φ : Formula n m) (a : Outside n m) (o : Occurrence m)
    (s : Bool) : Prop := Adj φ (outsideVertex a) (xor o (entryIndex s))
def leave {n m : Nat} (φ : Formula n m) (o : Occurrence m) (s : Bool)
    (a : Outside n m) : Prop := Adj φ (xor o (exitIndex s)) (outsideVertex a)
def link {n m : Nat} (φ : Formula n m) (o : Occurrence m) (s : Bool)
    (p : Occurrence m) (t : Bool) : Prop :=
  Adj φ (xor o (exitIndex s)) (xor p (entryIndex t))

def expanded {n m : Nat} (φ : Formula n m) (k : Nat) :
    ExpandedVertex n m k → ExpandedVertex n m k → Prop :=
  XorWire.network (outside φ) (enter φ) (leave φ) (link φ) k

/-- Relabel the original occurrence XOR as the sole section of a length-one
wire. Sentinels, variable vertices and clause vertices retain their labels. -/
def zeroEquiv (n m : Nat) : ExpandedVertex n m 0 ≃ Vertex n m where
  toFun := fun w => match w with
    | .inl a => outsideVertex a
    | .inr (o, (_, j)) => xor o j
  invFun := fun w => match w with
    | .inl i => .inl (.inl i)
    | .inr (.inl p) => .inl (.inr (.inl p))
    | .inr (.inr (.inl p)) => .inl (.inr (.inr p))
    | .inr (.inr (.inr (o, j))) => .inr (o, (0, j))
  left_inv := by
    rintro ((i | (p | p)) | ⟨o, i, j⟩)
    · rfl
    · rfl
    · rfl
    · have hi : i = 0 := by apply Fin.ext; omega
      cases hi
      rfl
  right_inv := by
    rintro (i | (p | (p | p))) <;> rfl

@[simp] theorem zeroEquiv_outside {n m : Nat} (a : Outside n m) :
    zeroEquiv n m (.inl a) = outsideVertex a := rfl
@[simp] theorem zeroEquiv_xor {n m : Nat} (o : Occurrence m) (w : XorWire.Vertex 0) :
    zeroEquiv n m (.inr (o, w)) = xor o w.2 := rfl

theorem zero_eq_entry (w : XorWire.Vertex 0) (s : Bool) :
    w = XorWire.entry 0 s ↔ w.2 = entryIndex s := by
  have h0 : w.1 = 0 := by apply Fin.ext; omega
  cases s <;> simp [XorWire.entry, entryIndex, Prod.ext_iff, h0]

theorem zero_eq_exit (w : XorWire.Vertex 0) (s : Bool) :
    w = XorWire.exit 0 s ↔ w.2 = exitIndex s := by
  have h0 : w.1 = 0 := by apply Fin.ext; omega
  cases s <;> simp [XorWire.exit, exitIndex, Prod.ext_iff, h0]

/-- Exact graph correspondence, including all inter-occurrence links. No
Hamiltonian-cycle assumption is used to identify the graphs. -/
theorem zero_adj_iff {n m : Nat} (φ : Formula n m) (u v : ExpandedVertex n m 0) :
    expanded φ 0 u v ↔ Adj φ (zeroEquiv n m u) (zeroEquiv n m v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => rfl
    | inr p =>
      rcases p with ⟨o, w⟩
      change (∃ b : Unit, ∃ s, enter φ a o s ∧ w = XorWire.entry 0 s) ↔
        Adj φ (outsideVertex a) (xor o w.2)
      simp only [zero_eq_entry, exists_const]
      constructor
      · rintro ⟨s, h, he⟩
        simpa [enter, he] using h
      · intro h
        rcases outside_to_xor_port φ a o w.2 h with he | he
        · exact ⟨true, by simpa [enter, entryIndex, ← he] using h, he⟩
        · exact ⟨false, by simpa [enter, entryIndex, ← he] using h, he⟩
  | inr p =>
    rcases p with ⟨o, w⟩
    cases v with
    | inl a =>
      change (∃ b : Unit, ∃ s, leave φ o s a ∧ w = XorWire.exit 0 s) ↔
        Adj φ (xor o w.2) (outsideVertex a)
      simp only [zero_eq_exit, exists_const]
      constructor
      · rintro ⟨s, h, he⟩
        simpa [leave, he] using h
      · intro h
        rcases xor_to_outside_port φ o w.2 a h with he | he
        · exact ⟨true, by simpa [leave, exitIndex, ← he] using h, he⟩
        · exact ⟨false, by simpa [leave, exitIndex, ← he] using h, he⟩
    | inr p =>
      rcases p with ⟨p, z⟩
      change ((o = p ∧ XorWire.Adj 0 w z) ∨
        (o ≠ p ∧ ∃ b : Unit, ∃ s, ∃ c : Unit, ∃ t,
          link φ o s p t ∧ w = XorWire.exit 0 s ∧ z = XorWire.entry 0 t)) ↔
        Adj φ (xor o w.2) (xor p z.2)
      simp only [zero_eq_exit, zero_eq_entry, exists_const, XorWire.zero_adj_iff]
      by_cases hop : o = p
      · subst p
        simpa using (xor_internal_iff φ o w.2 z.2).symm
      · simp only [ne_eq, hop, false_and, false_or, not_false_eq_true, true_and]
        constructor
        · rintro ⟨s, t, h, he, hf⟩
          simpa [link, he, hf] using h
        · intro h
          obtain ⟨hi, hj⟩ := xor_link_ports φ o p hop w.2 z.2 h
          rcases hi with he | he <;> rcases hj with hf | hf
          · exact ⟨true, true, by simpa [link, exitIndex, entryIndex, ← he, ← hf] using h,
              he, hf⟩
          · exact ⟨true, false, by simpa [link, exitIndex, entryIndex, ← he, ← hf] using h,
              he, hf⟩
          · exact ⟨false, true, by simpa [link, exitIndex, entryIndex, ← he, ← hf] using h,
              he, hf⟩
          · exact ⟨false, false, by simpa [link, exitIndex, entryIndex, ← he, ← hf] using h,
              he, hf⟩

/-- Arbitrary simultaneous stretching of the SAT construction's occurrence
XORs preserves exactly its satisfying assignments' existence. -/
theorem correct {n m : Nat} (φ : Formula n m) (k : Nat) :
    Satisfiable φ ↔ PathCover.Hamiltonian (expanded φ k) := by
  have hz : PathCover.Hamiltonian (expanded φ 0) ↔ PlanarSatReduction.Hamiltonian φ :=
    PathCover.hamiltonian_relabel_iff _ _ (zeroEquiv n m) (zero_adj_iff φ)
  exact (PlanarSatReduction.correct φ).trans (hz.symm.trans
    (XorWire.network_stretch_iff (outside φ) (enter φ) (leave φ) (link φ) 0 k))

theorem vertex_count (n m k : Nat) :
    Fintype.card (ExpandedVertex n m k) = 3 + 2 * n + 12 * m + 24 * m * (k + 1) := by
  simp [ExpandedVertex, Outside, Occurrence, XorWire.Vertex]
  ring

end GridHardness.SatWireExpansion
