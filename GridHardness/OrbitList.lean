/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrbitHamiltonian
public import Mathlib.Data.List.Chain

/-!
# Orbit List

Construct a single-orbit successor map from a cyclic enumeration of the vertices.
-/

public section

namespace GridHardness

/-- A list visiting every vertex once, with its last-to-first edge, yields an
actual successor permutation with one orbit. This turns explicitly spliced
gadget paths into a global directed Hamiltonian witness. -/
theorem oneOrbit_of_cyclic_list {V : Type*} (D : V → V → Prop)
    (l : List V) (hn : l.Nodup) (hcover : ∀ v, v ∈ l)
    (hne : l ≠ []) (hchain : l.IsChain D)
    (hclose : D (l.getLast hne) (l.head hne)) :
    ∃ next : V ≃ V, OneOrbit next ∧ ∀ v, D v (next v) := by
  let e : Fin l.length ≃ V := Equiv.ofBijective l.get
    ⟨hn.injective_get, fun v => List.mem_iff_get.mp (hcover v)⟩
  let next : V ≃ V := e.symm.trans ((finRotate _).trans e)
  have hstep : ∀ i, next (e i) = e (finRotate _ i) := by
    intro i
    simp [next]
  refine ⟨next, (oneOrbit_finRotate _).transport e hstep, ?_⟩
  suffices hs : ∀ i : Fin l.length, D (e i) (e (finRotate _ i)) by
    intro v
    simpa [next] using hs (e.symm v)
  intro i
  change D l[i.val] l[(finRotate _ i).val]
  have hval := val_finRotate i
  by_cases hi : i.val + 1 = l.length
  · have he : i.val = l.length - 1 := by omega
    rw [ite_eq_left hi] at hval
    simpa only [List.getLast_eq_getElem, List.head_eq_getElem, hval, he] using hclose
  · rw [ite_eq_right hi] at hval
    have hb : i.val + 1 < l.length := by have := i.isLt; omega
    simpa only [hval] using List.isChain_iff_getElem.mp hchain i.val hb

end GridHardness
