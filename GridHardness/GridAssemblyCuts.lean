/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedOrbit
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# Grid Assembly Cuts

Cut counting for the reverse direction of a grid gadget assembly.
These are global cycle facts: a proper nonempty region in one spanning
orbit has equally many entering and leaving edges, with at least one each.
In particular a region with at most three available boundary edges uses
exactly two. Geometry must establish the boundary bound for each gadget.
-/

@[expose] public section

namespace GridHardness.CycleCut

variable {V : Type*} [Fintype V] [DecidableEq V]

def leaving (next : Equiv.Perm V) (S : Finset V) : Finset V :=
  S.filter fun v => next v ∉ S

def entering (next : Equiv.Perm V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ S ∧ next v ∈ S

theorem balance (next : Equiv.Perm V) (S : Finset V) :
    (leaving next S).card = (entering next S).card := by
  let pre := Finset.univ.filter fun v => next v ∈ S
  let inside := S.filter fun v => next v ∈ S
  have hmap : pre.map next.toEmbedding = S := by
    ext v
    simp [pre]
  have hcard : pre.card = S.card := by
    rw [← Finset.card_map next.toEmbedding, hmap]
  have hin : pre.filter (fun v => v ∈ S) = inside := by
    ext v
    simp [pre, inside, and_comm]
  have hout : pre.filter (fun v => v ∉ S) = entering next S := by
    ext v
    simp [pre, entering, and_comm]
  have h1 := S.card_filter_add_card_filter_not (fun v => next v ∈ S)
  have h2 := pre.card_filter_add_card_filter_not (fun v => v ∈ S)
  change inside.card + (leaving next S).card = S.card at h1
  rw [hin, hout, hcard] at h2
  omega

omit [Fintype V] in
theorem leaving_nonempty (next : Equiv.Perm V) (ho : OneOrbit next)
    (S : Finset V) (hs : S.Nonempty) (hout : ∃ v, v ∉ S) :
    (leaving next S).Nonempty := by
  by_contra hn
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hout
  have hclosed : ∀ v, v ∈ S → next v ∈ S := by
    intro v hv
    by_contra hnxt
    exact hn ⟨v, Finset.mem_filter.mpr ⟨hv, hnxt⟩⟩
  exact hb (ho.closed_spans (P := fun v => v ∈ S) ha hclosed b)

/-- Three external attachments allow exactly one entrance and one exit.
Thus a three-port tentacle is crossed once or returns through its two
same-side attachments; a spanning cycle cannot strand a closed component. -/
theorem three_port_region (next : Equiv.Perm V) (ho : OneOrbit next)
    (S : Finset V) (hs : S.Nonempty) (hout : ∃ v, v ∉ S)
    (hports : (leaving next S).card + (entering next S).card ≤ 3) :
    (leaving next S).card = 1 ∧ (entering next S).card = 1 := by
  have he := balance next S
  have hp := Finset.card_pos.mpr (leaving_nonempty next ho S hs hout)
  omega

theorem even_crossings (next : Equiv.Perm V) (S : Finset V) :
    Even ((leaving next S).card + (entering next S).card) := by
  rw [balance]
  exact ⟨_, rfl⟩

end GridHardness.CycleCut
