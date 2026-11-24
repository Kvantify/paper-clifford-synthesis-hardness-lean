/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedOrbit

/-!
# Orbit Splicing

Reachability lemmas for replacing the vertices or edges of a spanning
cycle by finite directed routes. These express the actual global connectedness
obligation in addition to local degree constraints.
-/

@[expose] public section

namespace GridHardness

/-- Reachability by zero or more applications of a chosen successor. -/
def StepReach {V : Type*} (next : V → V) (u v : V) : Prop :=
  ∃ n : Nat, (next^[n]) u = v

theorem StepReach.refl {V : Type*} (next : V → V) (u : V) : StepReach next u u :=
  ⟨0, rfl⟩

theorem StepReach.step {V : Type*} (next : V → V) (u : V) :
    StepReach next u (next u) := ⟨1, rfl⟩

theorem StepReach.trans {V : Type*} {next : V → V} {u v w : V}
    (huv : StepReach next u v) (hvw : StepReach next v w) : StepReach next u w := by
  obtain ⟨m, hm⟩ := huv
  obtain ⟨n, hn⟩ := hvw
  exact ⟨n + m, by rw [Function.iterate_add_apply, hm, hn]⟩

/-- Lifting every individual step lifts any finite sequence of steps. -/
theorem StepReach.lift {V W : Type*} {next : V → V} {step : W → W}
    (entry : V → W) (hlift : ∀ v, StepReach step (entry v) (entry (next v)))
    {u v : V} (h : StepReach next u v) : StepReach step (entry u) (entry v) := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact StepReach.refl _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (hlift _)

/-- Replacing each base step by a directed route preserves the spanning
orbit, provided every new vertex can enter and leave the lifted backbone. -/
theorem OneOrbit.expand {V W : Type*} {next : V → V} {step : W → W}
    (h : OneOrbit next) (entry : V → W)
    (hlift : ∀ v, StepReach step (entry v) (entry (next v)))
    (henter : ∀ w, ∃ v, StepReach step w (entry v))
    (hcover : ∀ w, ∃ v, StepReach step (entry v) w) : OneOrbit step := by
  intro u w
  obtain ⟨v, hv⟩ := henter u
  obtain ⟨z, hz⟩ := hcover w
  exact (hv.trans (StepReach.lift entry hlift (h v z))).trans hz

/-- A route may spend several steps inside one gadget before advancing to
the next base vertex. Such stuttering does not obstruct cycle extraction. -/
theorem StepReach.project {V W : Type*} {next : V → V} {step : W → W}
    (label : W → V)
    (hstep : ∀ w, label (step w) = label w ∨ label (step w) = next (label w))
    {u w : W} (h : StepReach step u w) : StepReach next (label u) (label w) := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact StepReach.refl _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases hstep ((step^[n]) u) with hs | hs
    · rwa [hs]
    · rw [hs]
      exact ih.trans (StepReach.step _ _)

/-- A surjective projection whose steps stutter or follow the base successor
extracts a single spanning orbit from the expanded cycle. -/
theorem OneOrbit.project {V W : Type*} {next : V → V} {step : W → W}
    (h : OneOrbit step) (label : W → V) (hsurj : Function.Surjective label)
    (hstep : ∀ w, label (step w) = label w ∨ label (step w) = next (label w)) :
    OneOrbit next := by
  intro u v
  obtain ⟨a, rfl⟩ := hsurj u
  obtain ⟨b, rfl⟩ := hsurj v
  exact StepReach.project label hstep (h a b)

/-- An equivalent formulation useful when a gadget proof supplies closure
facts rather than an explicit bound on the number of successor steps. -/
theorem oneOrbit_iff_closed {V : Type*} (next : V → V) :
    OneOrbit next ↔ ∀ (P : V → Prop) (a : V), P a →
      (∀ v, P v → P (next v)) → ∀ v, P v := by
  constructor
  · intro h P a ha hc
    exact h.closed_spans ha hc
  · intro h a b
    exact h (StepReach next a) a (StepReach.refl _ _)
      (fun v hv => hv.trans (StepReach.step _ _)) b

end GridHardness
