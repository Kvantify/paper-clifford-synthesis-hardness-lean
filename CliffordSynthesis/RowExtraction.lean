/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Freshness

/-!
# Row Extraction

Extracting a classical elementary row-addition circuit from the actual
visible history, with exactly one row addition per paid Clifford gate.
-/

@[expose] public section

namespace CliffordSynthesis.RowExtraction

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic run applyGate CX)
open Observation (visible)
open PairInventory (event)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

structure AddGate (n : Nat) where
  control : Fin n
  target : Fin n
  distinct : control ≠ target

def addRow (g : AddGate n) (v : Fin n → V) : Fin n → V :=
  fun i => if i = g.target then v i + v g.control else v i

def runRows (gs : List (AddGate n)) : (Fin n → V) → (Fin n → V) :=
  gs.rec id (fun g _ tail v => tail (addRow g v))

/-- The ambient type-T formula yields one of the two orientations of a
classical elementary row addition, on the same labelled wires. -/
theorem T_row (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (v : Fin n → V)
    (hv : ∀ i, visible W a i = some (v i)) (c t : Fin n) (hct : c ≠ t)
    (he : event W a c t = .T) :
    ∃ g : AddGate n, (g.control = c ∧ g.target = t ∨ g.control = t ∧ g.target = c) ∧
      ∀ i, visible W (CX c t a) i = some (addRow g v i) := by
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  change (event W a c t).before = _ ∧ (event W a c t).after = _ ∧ (event W a c t).births = _ at hs
  rw [he] at hs
  have hsig : Observation.signature W a (CX c t a) c t = (2, 2, 1) :=
    Prod.ext hs.1.symm (Prod.ext hs.2.1.symm hs.2.2.symm)
  obtain ⟨u, w, hu, hw, hadd⟩ := Observation.cnot_rowAddition B W hW a ha c t hct hsig
  have hue : u = v c := Option.some.inj (hu.symm.trans (hv c))
  have hwe : w = v t := Option.some.inj (hw.symm.trans (hv t))
  rw [hue, hwe] at hadd
  rcases hadd with ⟨hc, ht⟩ | ⟨hc, ht⟩
  · refine ⟨⟨c, t, hct⟩, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro i
    by_cases hic : i = c
    · simpa [hic, addRow, hct] using hc
    by_cases hit : i = t
    · simpa [hit, addRow, add_comm] using ht
    · simpa [addRow, hit] using (Observation.cnot_untouched W a c t i hic hit).trans (hv i)
  · refine ⟨⟨t, c, Ne.symm hct⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
    intro i
    by_cases hic : i = c
    · simpa [hic, addRow] using hc
    by_cases hit : i = t
    · simpa [hit, addRow, Ne.symm hct] using ht
    · simpa [addRow, hic] using (Observation.cnot_untouched W a c t i hic hit).trans (hv i)

/-- The extracted circuit has exactly the paid length and its final rows are
the actual final visible vectors, in their physical wire order. -/
theorem extract (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (v : Fin n → V) (hv : ∀ i, visible W a i = some (v i))
    (hT : ∀ e ∈ CircuitLedger.trace W gs a, e = .T) :
    ∃ cs : List (AddGate n), cs.length = Circuit.cost gs ∧
      ∀ i, visible W (run gs a) i = some (runRows cs v i) := by
  induction gs generalizing a v with
  | nil => exact ⟨[], rfl, hv⟩
  | cons g gs ih =>
    have ha' := SymplecticCircuit.gate_symplectic B a ha g
    cases g with
    | H q =>
      have hv' : ∀ i, visible W (applyGate (.H q) a) i = some (v i) := by
        simpa only [applyGate, Observation.hadamard_visible B W hW a ha] using hv
      obtain ⟨cs, hlen, hout⟩ := ih _ ha' v hv' hT
      exact ⟨cs, by simpa [Circuit.cost, Circuit.paid] using hlen, hout⟩
    | S q =>
      have hv' : ∀ i, visible W (applyGate (.S q) a) i = some (v i) := by
        simpa only [applyGate, Observation.phase_visible B W hW a ha] using hv
      obtain ⟨cs, hlen, hout⟩ := ih _ ha' v hv' hT
      exact ⟨cs, by simpa [Circuit.cost, Circuit.paid] using hlen, hout⟩
    | CX c t hct =>
      have he : event W a c t = .T := hT _ (List.mem_cons_self)
      have ht : ∀ e ∈ CircuitLedger.trace W gs (CX c t a), e = .T :=
        fun e he => hT e (List.mem_cons_of_mem _ he)
      obtain ⟨g, _, hv'⟩ := T_row B W hW a ha v hv c t hct he
      obtain ⟨cs, hlen, hout⟩ := ih _ ha' (addRow g v) hv' ht
      refine ⟨g :: cs, ?_, hout⟩
      simp [Circuit.cost, Circuit.paid, hlen, Nat.add_comm]

/-- Saturated actual circuits admit the promised classical row circuit. -/
theorem actual_extract {r : Nat} (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (required : Fin r → StandardSpace.Space n) (hr : Function.Injective required)
    (hi : ∀ j i, (StandardSpace.standard n).x i ≠ required j)
    (hv : ∀ j, ∃ s ≤ gs.length, ∃ i,
      BirthOccurrences.atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i = some (required j))
    (hcost : Circuit.cost gs ≤ r) :
    ∃ cs : List (AddGate n), cs.length = r ∧
      ∀ i, visible (StandardSpace.initialW n)
        (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) i =
        some (runRows cs (StandardSpace.standard n).x i) := by
  obtain ⟨hcost', _, _, hT⟩ := Freshness.actual_required_all_T gs hlinear required hr hi hv hcost
  obtain ⟨cs, hlen, hout⟩ := extract (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
    (StandardSpace.standard n).x (CircuitLedger.initial_visible n) hT
  refine ⟨cs, hlen.trans hcost', ?_⟩
  simpa only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] using hout

end CliffordSynthesis.RowExtraction
