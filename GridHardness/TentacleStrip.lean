/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridGeometry
public import Mathlib.Data.List.ChainOfFn

/-!
# Tentacle Strip

Explicit Hamiltonian routes in a strip of arbitrary length.  A strip is
the induced integer grid on `{0,...,n} × {0,1}`.  The constructions below are
uniform in `n`; no bounded search or precomputed table is used.
-/

@[expose] public section

namespace GridHardness
open CliffordSynthesis SimpleGraph SimpleGraph.Walk
set_option backward.isDefEq.respectTransparency false

/-- A bijective adjacent enumeration gives an actual Hamiltonian walk. -/
theorem hamiltonian_of_enumeration {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {N : Nat} (hN : 0 < N)
    (f : Fin N → V) (hf : Function.Bijective f)
    (hs : ∀ i (hi : i + 1 < N),
      G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩)) :
    ∃ p : G.Walk (f ⟨0, hN⟩) (f ⟨N - 1, by omega⟩), p.IsHamiltonian := by
  have hne : List.ofFn f ≠ [] := by simp [List.ofFn_eq_nil_iff]; omega
  have hc : (List.ofFn f).IsChain G.Adj := List.isChain_ofFn.mpr hs
  let p := Walk.ofSupport (G := G) (List.ofFn f) hne hc
  have hp : p.IsHamiltonian := by
    apply Walk.IsPath.isHamiltonian_of_mem
    · rw [Walk.isPath_def, Walk.support_ofSupport]
      exact List.nodup_ofFn.mpr hf.injective
    · intro v
      rw [Walk.support_ofSupport]
      exact List.mem_ofFn.mpr (hf.surjective v)
  refine ⟨p.copy ?_ ?_, ?_⟩
  · exact List.head_ofFn hne
  · exact List.getLast_ofFn hne
  · simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp

namespace TentacleStrip

abbrev Vertex (n : Nat) := Fin (n + 1) × Fin 2

def point {n : Nat} (v : Vertex n) : Int × Int := (v.1.val, v.2.val)

def graph (n : Nat) : SimpleGraph (Vertex n) where
  Adj v w := IntegerGrid.manhattan (point v) (point w) = 1
  symm := ⟨by intro v w h; rwa [IntegerGrid.manhattan_comm]⟩
  loopless := ⟨by intro v; simp [IntegerGrid.manhattan]⟩

instance (n : Nat) : DecidableRel (graph n).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = (1 : Nat)))

theorem point_injective (n : Nat) : Function.Injective (@point n) := by
  intro v w h
  simpa [point, Prod.ext_iff, Fin.ext_iff] using h

/-- Column-wise zigzag, beginning at the lower left corner. -/
def crossOrder (n : Nat) (i : Fin (2 * (n + 1))) : Vertex n :=
  (⟨i.val / 2, by omega⟩, ⟨(i.val / 2 + i.val) % 2, Nat.mod_lt _ (by decide)⟩)

theorem crossOrder_bijective (n : Nat) : Function.Bijective (crossOrder n) := by
  constructor
  · intro i j h
    have hx := congrArg (fun v : Vertex n => v.1.val) h
    have hy := congrArg (fun v : Vertex n => v.2.val) h
    dsimp [crossOrder] at hx hy
    apply Fin.ext
    omega
  · intro v
    refine ⟨⟨2 * v.1.val + (v.2.val + v.1.val) % 2, by omega⟩, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp [crossOrder] <;> omega

theorem crossOrder_adjacent (n i : Nat) (hi : i + 1 < 2 * (n + 1)) :
    (graph n).Adj (crossOrder n ⟨i, by omega⟩) (crossOrder n ⟨i + 1, hi⟩) := by
  change IntegerGrid.manhattan _ _ = 1
  rw [manhattan_one_iff]
  simp only [point, crossOrder, Prod.mk.injEq]
  omega

def lowerLeft (n : Nat) : Vertex n := (0, 0)
def upperLeft (n : Nat) : Vertex n := (0, 1)
def farCorner (n : Nat) : Vertex n := (Fin.last n, ⟨(n + 1) % 2, by omega⟩)

theorem cross_route (n : Nat) :
    ∃ p : (graph n).Walk (lowerLeft n) (farCorner n), p.IsHamiltonian := by
  have h := hamiltonian_of_enumeration (graph n) (by omega : 0 < 2 * (n + 1))
    (crossOrder n) (crossOrder_bijective n) (crossOrder_adjacent n)
  have hs : crossOrder n ⟨0, by omega⟩ = lowerLeft n := by
    apply Prod.ext <;> apply Fin.ext <;> simp [crossOrder, lowerLeft]
  have ht : crossOrder n ⟨2 * (n + 1) - 1, by omega⟩ = farCorner n := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [crossOrder, farCorner] <;> omega
  obtain ⟨p, hp⟩ := h
  exact ⟨p.copy hs ht, by simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp⟩

/-- Bottom row out, top row back. -/
def returnOrder (n : Nat) (i : Fin (2 * (n + 1))) : Vertex n :=
  if h : i.val < n + 1 then (⟨i.val, h⟩, 0)
  else (⟨2 * (n + 1) - 1 - i.val, by omega⟩, 1)

theorem returnOrder_bijective (n : Nat) : Function.Bijective (returnOrder n) := by
  constructor
  · intro i j h
    have hx := congrArg (fun v : Vertex n => v.1.val) h
    have hy := congrArg (fun v : Vertex n => v.2.val) h
    dsimp [returnOrder] at hx hy
    split_ifs at hx hy <;> apply Fin.ext <;> simp_all <;> omega
  · intro v
    by_cases hy : v.2.val = 0
    · refine ⟨⟨v.1.val, by omega⟩, ?_⟩
      simp only [returnOrder, v.1.is_lt, dite_true]
      apply Prod.ext
      · rfl
      · apply Fin.ext; simpa using hy.symm
    · refine ⟨⟨2 * (n + 1) - 1 - v.1.val, by omega⟩, ?_⟩
      rw [returnOrder, dite_eq_right (by dsimp; omega)]
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

theorem returnOrder_adjacent (n i : Nat) (hi : i + 1 < 2 * (n + 1)) :
    (graph n).Adj (returnOrder n ⟨i, by omega⟩) (returnOrder n ⟨i + 1, hi⟩) := by
  change IntegerGrid.manhattan _ _ = 1
  rw [manhattan_one_iff]
  simp only [returnOrder]
  split_ifs <;> simp only [point, Prod.mk.injEq, Fin.val_zero, Fin.val_one] <;>
    dsimp at * <;> simp_all <;> omega

theorem return_route (n : Nat) :
    ∃ p : (graph n).Walk (lowerLeft n) (upperLeft n), p.IsHamiltonian := by
  have h := hamiltonian_of_enumeration (graph n) (by omega : 0 < 2 * (n + 1))
    (returnOrder n) (returnOrder_bijective n) (returnOrder_adjacent n)
  have hs : returnOrder n ⟨0, by omega⟩ = lowerLeft n := by
    simp [returnOrder, lowerLeft]
  have ht : returnOrder n ⟨2 * (n + 1) - 1, by omega⟩ = upperLeft n := by
    rw [returnOrder, dite_eq_right (by dsimp; omega)]
    apply Prod.ext <;> apply Fin.ext <;> dsimp [upperLeft] <;> omega
  obtain ⟨p, hp⟩ := h
  exact ⟨p.copy hs ht, by simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp⟩

/-- The usual checkerboard coloring, written as a residue in `{0,1}`. -/
def parity {n : Nat} (v : Vertex n) : Nat := (v.1.val + v.2.val) % 2

theorem adjacent_parity {n : Nat} {u v : Vertex n} (h : (graph n).Adj u v) :
    (parity u + 1) % 2 = parity v := by
  change IntegerGrid.manhattan _ _ = 1 at h
  rw [manhattan_one_iff] at h
  simp only [point, Prod.mk.injEq] at h
  unfold parity
  omega

theorem walk_parity {n : Nat} {u v : Vertex n} (p : (graph n).Walk u v) :
    (parity u + p.length) % 2 = parity v := by
  induction p with
  | nil => simp [parity]
  | @cons u v w h p ih =>
    have ha := adjacent_parity h
    simp only [Walk.length_cons]
    unfold parity at *
    omega

theorem hamiltonian_opposite_parity {n : Nat} {u v : Vertex n}
    {p : (graph n).Walk u v} (hp : p.IsHamiltonian) : parity u ≠ parity v := by
  have h := walk_parity p
  have hl := hp.length_eq
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin] at hl
  unfold parity at *
  omega

/-- Reflection in the horizontal midline is an automorphism of the induced grid. -/
def verticalReflection (n : Nat) : graph n ≃g graph n where
  toEquiv := Equiv.prodCongr (Equiv.refl _) Fin.revPerm
  map_rel_iff' := by
    intro v w
    change IntegerGrid.manhattan (point (v.1, v.2.rev)) (point (w.1, w.2.rev)) = 1 ↔
      IntegerGrid.manhattan (point v) (point w) = 1
    simp only [IntegerGrid.manhattan, point, Fin.val_rev]
    omega

/-- Reflection in the vertical midline is an automorphism of the induced grid. -/
def horizontalReflection (n : Nat) : graph n ≃g graph n where
  toEquiv := Equiv.prodCongr Fin.revPerm (Equiv.refl _)
  map_rel_iff' := by
    intro v w
    change IntegerGrid.manhattan (point (v.1.rev, v.2)) (point (w.1.rev, w.2)) = 1 ↔
      IntegerGrid.manhattan (point v) (point w) = 1
    simp only [IntegerGrid.manhattan, point, Fin.val_rev]
    omega

theorem cross_route_between (n : Nat) (r t : Fin 2)
    (hpar : (r.val + n + t.val) % 2 = 1) :
    ∃ p : (graph n).Walk (0, r) (Fin.last n, t), p.IsHamiltonian := by
  have hr := r.is_lt
  rcases cross_route n with ⟨p, hp⟩
  by_cases h : r.val = 0
  · have hs : lowerLeft n = (0, r) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; exact h.symm
    have ht : farCorner n = (Fin.last n, t) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [farCorner]; omega
    exact ⟨p.copy hs ht, by simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp⟩
  · let e := verticalReflection n
    have hs : e (lowerLeft n) = (0, r) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; change 1 - 0 = r.val; omega
    have ht : e (farCorner n) = (Fin.last n, t) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change ((farCorner n).2.rev).val = t.val
        rw [Fin.val_rev]
        dsimp [farCorner]
        omega
    refine ⟨(p.map e.toHom).copy hs ht, ?_⟩
    simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp.map (f := e.toHom) e.bijective

theorem return_route_between (n : Nat) (r t : Fin 2) (hrt : r ≠ t) :
    ∃ p : (graph n).Walk (0, r) (0, t), p.IsHamiltonian := by
  rcases return_route n with ⟨p, hp⟩
  fin_cases r <;> fin_cases t
  · exact False.elim (hrt rfl)
  · exact ⟨p, hp⟩
  · exact ⟨p.reverse, by simpa [Walk.IsHamiltonian] using hp⟩
  · exact False.elim (hrt rfl)

def corner (n : Nat) (side row : Fin 2) : Vertex n :=
  (if side.val = 0 then 0 else Fin.last n, row)

/-- The one-strip case of [ItaiPapadimitriouSzwarcfiter1982, Lemma 2.4],
including both directions and every choice of corner endpoints. -/
theorem corner_route_iff (n : Nat) (a b r t : Fin 2) :
    (∃ p : (graph n).Walk (corner n a r) (corner n b t), p.IsHamiltonian) ↔
      parity (corner n a r) ≠ parity (corner n b t) := by
  constructor
  · rintro ⟨p, hp⟩
    exact hamiltonian_opposite_parity hp
  · intro h
    fin_cases a <;> fin_cases b <;> simp only [corner,
      ite_true, ite_false, Nat.one_ne_zero] at *
    · exact return_route_between n r t (by intro he; exact h (congrArg parity (by rw [he])))
    · exact cross_route_between n r t (by unfold parity at h; dsimp at h; omega)
    · rcases cross_route_between n t r (by unfold parity at h; dsimp at h; omega) with ⟨p, hp⟩
      exact ⟨p.reverse, by simpa [Walk.IsHamiltonian] using hp⟩
    · have hrt : r ≠ t := by intro he; exact h (congrArg parity (by rw [he]))
      rcases return_route_between n r t hrt with ⟨p, hp⟩
      let e := horizontalReflection n
      have hs : e (0, r) = (Fin.last n, r) := by
        apply Prod.ext
        · apply Fin.ext; simp [e, horizontalReflection, Fin.rev]
        · rfl
      have ht : e (0, t) = (Fin.last n, t) := by
        apply Prod.ext
        · apply Fin.ext; simp [e, horizontalReflection, Fin.rev]
        · rfl
      refine ⟨(p.map e.toHom).copy hs ht, ?_⟩
      simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp.map (f := e.toHom) e.bijective

/-- The near-boundary route needed at a right-angle junction.  Swapping the
first and third vertices of the reflected zigzag changes its prefix to
`(1,0), (0,0), (0,1), (1,1)` and leaves the remaining columns unchanged. -/
def offsetOrder (n : Nat) (hn : 1 ≤ n) (i : Fin (2 * (n + 1))) : Vertex n :=
  verticalReflection n (crossOrder n (Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩ i))

theorem offsetOrder_bijective (n : Nat) (hn : 1 ≤ n) :
    Function.Bijective (offsetOrder n hn) :=
  (verticalReflection n).bijective.comp ((crossOrder_bijective n).comp
    (Equiv.swap (⟨0, by omega⟩ : Fin (2 * (n + 1))) ⟨2, by omega⟩).bijective)

theorem offsetOrder_adjacent (n : Nat) (hn : 1 ≤ n) (i : Nat)
    (hi : i + 1 < 2 * (n + 1)) :
    (graph n).Adj (offsetOrder n hn ⟨i, by omega⟩) (offsetOrder n hn ⟨i + 1, hi⟩) := by
  by_cases his : i < 3
  · have hmod : 1 % (2 * (n + 1)) = 1 := Nat.mod_eq_of_lt (by omega)
    interval_cases i <;>
      simp [offsetOrder, Equiv.swap_apply_def, verticalReflection, crossOrder,
        graph, point, IntegerGrid.manhattan, Fin.rev, hmod]
  · have h0 : (⟨i, by omega⟩ : Fin (2 * (n + 1))) ≠ ⟨0, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    have h2 : (⟨i, by omega⟩ : Fin (2 * (n + 1))) ≠ ⟨2, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    have h0' : (⟨i + 1, hi⟩ : Fin (2 * (n + 1))) ≠ ⟨0, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    have h2' : (⟨i + 1, hi⟩ : Fin (2 * (n + 1))) ≠ ⟨2, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    simp only [offsetOrder, Equiv.swap_apply_of_ne_of_ne h0 h2,
      Equiv.swap_apply_of_ne_of_ne h0' h2']
    exact (verticalReflection n).toHom.map_adj (crossOrder_adjacent n i hi)

theorem offset_cross_route (n : Nat) (hn : 1 ≤ n) :
    ∃ p : (graph n).Walk (⟨1, by omega⟩, 0)
      (Fin.last n, ⟨n % 2, by omega⟩), p.IsHamiltonian := by
  rcases hamiltonian_of_enumeration (graph n) (by omega : 0 < 2 * (n + 1))
    (offsetOrder n hn) (offsetOrder_bijective n hn) (offsetOrder_adjacent n hn)
    with ⟨p, hp⟩
  have hs : offsetOrder n hn ⟨0, by omega⟩ = (⟨1, by omega⟩, 0) := by
    simp [offsetOrder, verticalReflection, crossOrder, Fin.rev]
  have ht : offsetOrder n hn ⟨2 * (n + 1) - 1, by omega⟩ =
      (Fin.last n, ⟨n % 2, by omega⟩) := by
    have h0 : (⟨2 * (n + 1) - 1, by omega⟩ : Fin (2 * (n + 1))) ≠ ⟨0, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    have h2 : (⟨2 * (n + 1) - 1, by omega⟩ : Fin (2 * (n + 1))) ≠ ⟨2, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    simp only [offsetOrder, Equiv.swap_apply_of_ne_of_ne h0 h2]
    apply Prod.ext
    · apply Fin.ext
      change (2 * (n + 1) - 1) / 2 = n
      omega
    · apply Fin.ext
      change 2 - (((2 * (n + 1) - 1) / 2 + (2 * (n + 1) - 1)) % 2 + 1) = n % 2
      omega
  exact ⟨p.copy hs ht, by simpa only [Walk.IsHamiltonian, Walk.support_copy] using hp⟩

end TentacleStrip
end GridHardness
