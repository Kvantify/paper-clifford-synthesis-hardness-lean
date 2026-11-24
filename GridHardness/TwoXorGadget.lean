/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatXor

/-!
# Two XOR Gadget

Two independent XOR gadgets, with the same four selectable entry/exit
pairs as the 56-vertex crossover. The classification below is derived from
an ambient Hamiltonian permutation and ordinary incident-edge isolation.
In particular, the second component provides a vertex outside the first,
and vice versa, so the XOR's forbidden cycles cannot be global cycles.
-/

@[expose] public section

namespace GridHardness.TwoXorGadget

abbrev Vertex := Bool × Fin 8

def x (comp : Bool) (i : Fin 8) : Vertex := (comp, i)

def Adj (u v : Vertex) : Prop :=
  u.1 = v.1 ∧ ∃ e : Fin 10, XorGadget.arc e = (u.2, v.2)

instance : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def entries : List Vertex := [x false 3, x false 4, x true 3, x true 4]
def exits : List Vertex := [x false 0, x false 7, x true 0, x true 7]

def route (choice : Bool) : XorGadget.Selection :=
  if choice then XorGadget.leftRoute else XorGadget.rightRoute

def path (comp choice : Bool) : List Vertex :=
  (if choice then XorGadget.leftVertices else XorGadget.rightVertices).map (x comp)

def entry (comp choice : Bool) : Vertex := x comp (if choice then 3 else 4)
def exit (comp choice : Bool) : Vertex := x comp (if choice then 0 else 7)

def horizontalPath (left : Bool) : List Vertex := path false left
def verticalPath (top : Bool) : List Vertex := path true top
def horizontalEntry (left : Bool) : Vertex := entry false left
def horizontalExit (left : Bool) : Vertex := exit false left
def verticalEntry (top : Bool) : Vertex := entry true top
def verticalExit (top : Bool) : Vertex := exit true top

def pathLinks (left top : Bool) : List (Vertex × Vertex) :=
  (horizontalPath left).zip (horizontalPath left).tail ++
    (verticalPath top).zip (verticalPath top).tail

theorem vertex_card : Fintype.card Vertex = 16 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem path_certificate : ∀ left top : Bool,
    (horizontalPath left).IsChain Adj ∧ (verticalPath top).IsChain Adj ∧
    (horizontalPath left).head? = some (horizontalEntry left) ∧
    (horizontalPath left).getLast? = some (horizontalExit left) ∧
    (verticalPath top).head? = some (verticalEntry top) ∧
    (verticalPath top).getLast? = some (verticalExit top) ∧
    (horizontalPath left).length = 8 ∧ (verticalPath top).length = 8 ∧
    ∀ v : Vertex, (horizontalPath left).count v + (verticalPath top).count v = 1 := by
  decide

structure Isolated {V : Type*} (succ : V → V) (embed : Vertex → V) : Prop where
  internal : ∀ u v, succ (embed u) = embed v → Adj u v
  outgoing : ∀ u, u ∉ exits → ∃ v, succ (embed u) = embed v
  incoming : ∀ v, v ∉ entries → ∃ u, succ (embed u) = embed v

theorem x_injective (comp : Bool) : Function.Injective (x comp) := by
  intro i j h
  exact congrArg Prod.snd h

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem x_nonexit : ∀ (comp : Bool) (i : Fin 8), i ≠ 0 → i ≠ 7 →
    x comp i ∉ exits := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem x_nonentry : ∀ (comp : Bool) (i : Fin 8), i ≠ 3 → i ≠ 4 →
    x comp i ∉ entries := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem x_outgoing : ∀ (comp : Bool) (i : Fin 8) (v : Vertex),
    Adj (x comp i) v ↔ ∃ e : Fin 10,
      (XorGadget.arc e).1 = i ∧ v = x comp (XorGadget.arc e).2 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem x_incoming : ∀ (comp : Bool) (i : Fin 8) (u : Vertex),
    Adj u (x comp i) ↔ ∃ e : Fin 10,
      (XorGadget.arc e).2 = i ∧ u = x comp (XorGadget.arc e).1 := by decide

/-- Each component has one of the two XOR routes. The vertex in the other
component rules out every internally closed cycle. -/
theorem component_selection {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) (comp : Bool) :
    PlanarSatXor.selection succ (embed ∘ x comp) = XorGadget.leftRoute ∨
      PlanarSatXor.selection succ (embed ∘ x comp) = XorGadget.rightRoute := by
  have hd : XorGadget.DegreeOK (PlanarSatXor.selection succ (embed ∘ x comp)) := by
    apply PlanarSatXor.degree_of_isolation succ (embed ∘ x comp)
      (he.comp (x_injective comp))
    · intro i hi0 hi7
      obtain ⟨v, hv⟩ := hg.outgoing (x comp i) (x_nonexit comp i hi0 hi7)
      obtain ⟨e, he', rfl⟩ := (x_outgoing comp i v).mp (hg.internal _ _ hv)
      exact ⟨e, he', hv⟩
    · intro i hi3 hi4
      obtain ⟨u, hu⟩ := hg.incoming (x comp i) (x_nonentry comp i hi3 hi4)
      obtain ⟨e, he', rfl⟩ := (x_incoming comp i u).mp (hg.internal _ _ hu)
      exact ⟨e, he', hu⟩
  exact XorGadget.selection_of_oneOrbit succ ho (embed ∘ x comp)
    (embed (x (!comp) 0))
    (fun i hi => by have hh := congrArg Prod.fst (he hi); simpa [x] using hh)
    (PlanarSatXor.selection succ (embed ∘ x comp)) hd
    (fun e hb => (PlanarSatXor.selection_true _ _ _).mp hb)

def Used (left top : Bool) (u v : Vertex) : Prop :=
  u.1 = v.1 ∧ XorGadget.Uses (route (if u.1 then top else left)) u.2 v.2

instance (left top : Bool) : DecidableRel (Used left top) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem used_certificate : ∀ left top : Bool,
    (horizontalPath left).IsChain (Used left top) ∧
    (verticalPath top).IsChain (Used left top) ∧
    (∀ u v, Used left top u v ↔ (u, v) ∈ pathLinks left top) ∧
    (∀ u, (∀ v, ¬ Used left top u v) ↔
      u = horizontalExit left ∨ u = verticalExit top) ∧
    (∀ v, (∀ u, ¬ Used left top u v) ↔
      v = horizontalEntry left ∨ v = verticalEntry top) := by decide

theorem internal_step_iff {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (embed : Vertex → V) (hg : Isolated succ embed) (left top : Bool)
    (hs : ∀ comp : Bool, PlanarSatXor.selection succ (embed ∘ x comp) =
      route (if comp then top else left)) :
    ∀ u v, succ (embed u) = embed v ↔ Used left top u v := by
  rintro ⟨c, i⟩ ⟨d, j⟩
  constructor
  · intro hstep
    obtain ⟨hcd, e, ha⟩ := hg.internal _ _ hstep
    dsimp at hcd ha
    subst d
    refine ⟨rfl, e, ?_, ha⟩
    rw [← hs c]
    apply (PlanarSatXor.selection_true _ _ _).mpr
    simpa [Function.comp_def, x, ha] using hstep
  · rintro ⟨hcd, e, hb, ha⟩
    dsimp at hcd ha
    subst d
    rw [← hs c] at hb
    have hstep := (PlanarSatXor.selection_true _ _ _).mp hb
    simpa [Function.comp_def, x, ha] using hstep

/-- The actual successor restricted to both isolated XORs consists exactly
of the two selected spanning paths, including their boundary incidences. -/
theorem route_classification {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) : ∃ left top : Bool,
    (horizontalPath left).IsChain (fun u v => succ (embed u) = embed v) ∧
    (verticalPath top).IsChain (fun u v => succ (embed u) = embed v) ∧
    (∀ u v, succ (embed u) = embed v ↔ (u, v) ∈ pathLinks left top) ∧
    (∀ u, (∀ v, succ (embed u) ≠ embed v) ↔
      u = horizontalExit left ∨ u = verticalExit top) ∧
    (∀ v, (∀ u, succ (embed u) ≠ embed v) ↔
      v = horizontalEntry left ∨ v = verticalEntry top) := by
  have hchoices : ∀ comp : Bool, ∃ choice : Bool,
      PlanarSatXor.selection succ (embed ∘ x comp) = route choice := by
    intro comp
    rcases component_selection succ ho embed he hg comp with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨left, hl⟩ := hchoices false
  obtain ⟨top, ht⟩ := hchoices true
  have hs : ∀ comp : Bool, PlanarSatXor.selection succ (embed ∘ x comp) =
      route (if comp then top else left) := by
    intro comp
    cases comp
    · exact hl
    · exact ht
  have hi := internal_step_iff succ embed hg left top hs
  obtain ⟨hh, hv, hp, ho', hi'⟩ := used_certificate left top
  refine ⟨left, top, hh.imp (fun u v huv => (hi u v).mpr huv),
    hv.imp (fun u v huv => (hi u v).mpr huv), ?_, ?_, ?_⟩
  · intro u v
    exact (hi u v).trans (hp u v)
  · intro u
    simpa only [ne_eq, hi] using ho' u
  · intro v
    simpa only [ne_eq, hi] using hi' v

end GridHardness.TwoXorGadget
