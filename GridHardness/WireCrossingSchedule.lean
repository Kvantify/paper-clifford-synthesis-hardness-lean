/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PermutationWireLayout
public import GridHardness.XorWireNetwork

/-!
# Wire Crossing Schedule

Allocate a distinct XOR section to each geometric crossing of the
permutation wire layout. Vertical crossings are ordered by exit height;
horizontal crossings are ordered by decreasing column. The two section
ranges are disjoint, and a spare final section keeps horizontal crossing
sections away from both external ends of their wire.
-/

@[expose] public section

namespace GridHardness.WireCrossingSchedule

section
variable {N : Nat} (p : Equiv.Perm (Fin N))

abbrev Cell := {ij : Fin N × Fin N // ij.1 < ij.2 ∧ p ij.2 < p ij.1}

/-- `false` is the horizontal crossover channel, `true` the vertical one. -/
def wire (c : Cell p) (b : Bool) : Fin N := if b then c.1.1 else c.1.2

def sectionIndex (c : Cell p) (b : Bool) : Fin (2*N+1) :=
  if b then ⟨(p c.1.2).val, by have := (p c.1.2).isLt; omega⟩
  else ⟨N + (N-1-c.1.1.val), by have := c.1.1.isLt; omega⟩

def slot (cb : Cell p × Bool) : Fin N × Fin (2*N+1) :=
  (wire p cb.1 cb.2, sectionIndex p cb.1 cb.2)

theorem vertical_section_lt (c : Cell p) : (sectionIndex p c true).val < N :=
  (p c.1.2).isLt

theorem horizontal_section_bounds (c : Cell p) :
    N ≤ (sectionIndex p c false).val ∧ (sectionIndex p c false).val < 2*N := by
  have := c.1.1.isLt
  dsimp [sectionIndex]
  omega

theorem channels_distinct (c : Cell p) : wire p c false ≠ wire p c true := by
  exact (ne_of_lt c.2.1).symm

/-- All crossing channels occupy distinct sections, including crossings
sharing one of their two wires. -/
theorem slot_injective : Function.Injective (slot p) := by
  rintro ⟨c, b⟩ ⟨d, t⟩ h
  have hw := congrArg Prod.fst h
  have hs := congrArg (fun z : Fin N × Fin (2*N+1) => z.2.val) h
  cases b <;> cases t
  · have hj : c.1.2 = d.1.2 := hw
    have hi : c.1.1 = d.1.1 := by
      apply Fin.ext
      have := c.1.1.isLt
      have := d.1.1.isLt
      dsimp [slot, sectionIndex] at hs
      omega
    have hc : c = d := Subtype.ext (Prod.ext hi hj)
    cases hc
    rfl
  · have ha := horizontal_section_bounds p c
    have hb := vertical_section_lt p d
    dsimp [slot] at hs
    omega
  · have ha := vertical_section_lt p c
    have hb := horizontal_section_bounds p d
    dsimp [slot] at hs
    omega
  · have hi : c.1.1 = d.1.1 := hw
    have hj : c.1.2 = d.1.2 := by
      apply p.injective
      apply Fin.ext
      exact hs
    have hc : c = d := Subtype.ext (Prod.ext hi hj)
    cases hc
    rfl

def place (cv : Cell p × (Bool × Fin 8)) : Fin N × XorWire.Vertex (2*N) :=
  (wire p cv.1 cv.2.1, (sectionIndex p cv.1 cv.2.1, cv.2.2))

theorem place_injective : Function.Injective (place p) := by
  rintro ⟨c, b, i⟩ ⟨d, t, j⟩ h
  have hs : slot p (c, b) = slot p (d, t) :=
    congrArg (fun z : Fin N × XorWire.Vertex (2*N) => (z.1, z.2.1)) h
  have hcb := slot_injective p hs
  have hij : i = j := congrArg (fun z : Fin N × XorWire.Vertex (2*N) => z.2.2) h
  cases hcb
  cases hij
  rfl

/-- Horizontal crossing sections are interior sections of the long wire,
so a boundary link cannot create an unwanted internal edge of the pair. -/
theorem horizontal_not_boundary (c : Cell p) :
    sectionIndex p c false ≠ 0 ∧ sectionIndex p c false ≠ Fin.last (2*N) := by
  have hn : 0 < N := by have := c.1.1.isLt; omega
  have hb := horizontal_section_bounds p c
  constructor <;> intro h <;> have he := congrArg Fin.val h <;> simp only [Fin.val_zero, Fin.val_last] at he <;> omega

/-- Vertical sections appear in exactly the increasing-height order of the
crossings along their centerline. -/
theorem vertical_order (c d : Cell p) :
    sectionIndex p c true < sectionIndex p d true ↔ p c.1.2 < p d.1.2 := Iff.rfl

/-- Horizontal sections appear in exactly decreasing-column order. -/
theorem horizontal_order (c d : Cell p) :
    sectionIndex p c false < sectionIndex p d false ↔ d.1.1 < c.1.1 := by
  have := c.1.1.isLt
  have := d.1.1.isLt
  change N+(N-1-c.1.1.val) < N+(N-1-d.1.1.val) ↔ d.1.1.val < c.1.1.val
  omega

end
end GridHardness.WireCrossingSchedule
