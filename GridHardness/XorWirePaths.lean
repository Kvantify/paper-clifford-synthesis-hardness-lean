/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWire
public import GridHardness.TwoPathCover

/-!
# XOR Wire Paths

Order the vertices of local and section traversals in the XOR wire graph.
-/

@[expose] public section

namespace GridHardness.XorWire
open PathCover

def localOrder (choice : Bool) : Equiv.Perm (Fin 8) where
  toFun := if choice then ![3, 7, 6, 2, 1, 5, 4, 0] else ![4, 0, 1, 5, 6, 2, 3, 7]
  invFun := if choice then ![7, 4, 3, 0, 6, 5, 2, 1] else ![1, 2, 5, 6, 0, 3, 4, 7]
  left_inv := by cases choice <;> decide
  right_inv := by cases choice <;> decide

def sectionOrder (n : Nat) (choice : Bool) : Equiv.Perm (Fin (n + 1)) :=
  if choice then Equiv.refl _ else Fin.revPerm

def orderEquiv (n : Nat) (choice : Bool) : Fin ((n + 1) * 8) ≃ Vertex n :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (sectionOrder n choice) (localOrder choice))

theorem order_component (n : Nat) (choice : Bool) (k : Fin ((n + 1) * 8)) :
    (orderEquiv n choice k).1.val = if choice then k.val / 8 else n - k.val / 8 := by
  cases choice
  · change (n + 1) - (k.val / 8 + 1) = n - k.val / 8
    omega
  · rfl

theorem order_eq (n : Nat) (choice : Bool) (k : Fin ((n + 1) * 8))
    (i : Fin (n + 1)) (j : Fin 8)
    (hi : (if choice then k.val / 8 else n - k.val / 8) = i.val)
    (hj : k.val % 8 = j.val) : orderEquiv n choice k = (i, localOrder choice j) := by
  apply Prod.ext
  · exact Fin.ext ((order_component n choice k).trans hi)
  · apply congrArg (localOrder choice)
    exact Fin.ext hj

def pathSize (n : Nat) : Nat := (n + 1) * 8 - 1

theorem pathSize_add_one (n : Nat) : pathSize n + 1 = (n + 1) * 8 := by
  unfold pathSize
  omega

/-- The entire wire is one ordered path, in increasing or decreasing
section order according to its selected signal. -/
def cover (n : Nat) (choice : Bool) : Cover Unit (Vertex n) where
  size := fun _ => pathSize n
  equiv :=
    { toFun := fun w => orderEquiv n choice (Fin.cast (pathSize_add_one n) w.2)
      invFun := fun v => ⟨(), Fin.cast (pathSize_add_one n).symm ((orderEquiv n choice).symm v)⟩
      left_inv := by rintro ⟨⟨⟩, i⟩; simp
      right_inv := by intro v; simp }

theorem cover_first (n : Nat) (choice : Bool) : (cover n choice).first () = entry n choice := by
  change orderEquiv n choice _ = _
  cases choice
  · change orderEquiv n false _ = (Fin.last n, localOrder false 0)
    apply order_eq
    · change n - 0 / 8 = n; omega
    · rfl
  · change orderEquiv n true _ = (0, localOrder true 0)
    apply order_eq
    · change 0 / 8 = (0 : Fin (n + 1)).val; simp
    · rfl

theorem cover_finish (n : Nat) (choice : Bool) : (cover n choice).finish () = exit n choice := by
  change orderEquiv n choice _ = _
  have hd : pathSize n / 8 = n := by unfold pathSize; omega
  have hm : pathSize n % 8 = 7 := by unfold pathSize; omega
  cases choice
  · change orderEquiv n false _ = (0, localOrder false 7)
    apply order_eq
    · change n - pathSize n / 8 = 0; rw [hd]; omega
    · exact hm
  · change orderEquiv n true _ = (Fin.last n, localOrder true 7)
    apply order_eq
    · exact hd
    · exact hm

/-- General concatenation rule: local seven-edge routes plus the links
between consecutive sections give every edge of the full spanning path. -/
theorem cover_internalEdges (n : Nat) (choice : Bool) (R : Vertex n → Vertex n → Prop)
    (hlocal : ∀ (i : Fin (n + 1)) (j : Fin 7),
      R (i, localOrder choice j.castSucc) (i, localOrder choice j.succ))
    (hcross : ∀ i : Fin n,
      R (if choice then (i.castSucc, 0) else (i.succ, 7))
        (if choice then (i.succ, 3) else (i.castSucc, 4))) :
    (cover n choice).InternalEdges R := by
  have hstep : ∀ a b : Fin ((n + 1) * 8), b.val = a.val + 1 →
      R (orderEquiv n choice a) (orderEquiv n choice b) := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    by_cases hm : a.val % 8 < 7
    · let i : Fin (n + 1) := ⟨if choice then a.val / 8 else n - a.val / 8,
        by cases choice <;> simp <;> omega⟩
      let j : Fin 7 := ⟨a.val % 8, hm⟩
      have ea : orderEquiv n choice a = (i, localOrder choice j.castSucc) :=
        order_eq n choice a i j.castSucc rfl rfl
      have eb : orderEquiv n choice b = (i, localOrder choice j.succ) := by
        apply order_eq
        · cases choice <;> simp [i] <;> omega
        · simp [j]; omega
      rw [ea, eb]
      exact hlocal i j
    · have hmod : a.val % 8 = 7 := by omega
      cases choice
      · let i : Fin n := ⟨n - a.val / 8 - 1, by omega⟩
        have ea : orderEquiv n false a = (i.succ, localOrder false 7) := by
          apply order_eq <;> simp [i] <;> omega
        have eb : orderEquiv n false b = (i.castSucc, localOrder false 0) := by
          apply order_eq <;> simp [i] <;> omega
        rw [ea, eb]
        exact hcross i
      · let i : Fin n := ⟨a.val / 8, by omega⟩
        have ea : orderEquiv n true a = (i.castSucc, localOrder true 7) := by
          apply order_eq <;> simp [i] <;> omega
        have eb : orderEquiv n true b = (i.succ, localOrder true 0) := by
          apply order_eq <;> simp [i] <;> omega
        rw [ea, eb]
        exact hcross i
  rintro ⟨⟩ j
  exact hstep _ _ rfl

theorem local_route_steps : ∀ (choice : Bool) (j : Fin 7),
    XorGadget.Uses (route choice) (localOrder choice j.castSucc) (localOrder choice j.succ) := by
  decide

theorem cover_adjacent (n : Nat) (choice : Bool) : (cover n choice).InternalEdges (Adj n) := by
  apply cover_internalEdges
  · intro i j
    obtain ⟨e, _, he⟩ := local_route_steps choice j
    exact Or.inl ⟨rfl, e, he⟩
  · intro i
    cases choice
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

/-- An actual Hamiltonian successor follows all edges of one complete wire
route. Its section choices and links are derived from the isolated graph. -/
theorem route_classification {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ choice : Bool, (cover n choice).InternalEdges (fun u v => succ (embed u) = embed v) := by
  obtain ⟨choice, hc⟩ := uniform_selection succ ho embed he hg
  refine ⟨choice, cover_internalEdges n choice _ ?_ ?_⟩
  · intro i j
    obtain ⟨e, hs, ha⟩ := local_route_steps choice j
    rw [← hc i] at hs
    have hh := (PlanarSatXor.selection_true succ (fun j => embed (i, j)) e).mp hs
    simpa [ha] using hh
  · intro i
    cases choice
    · exact reverse_link succ embed hg i (hc i.succ)
    · exact forward_link succ embed hg i (hc i.castSucc)

/-- A list view of the explicit spanning route, useful for direct graph
constructions as well as the path-cover replacement theorem. -/
def path (n : Nat) (choice : Bool) : List (Vertex n) :=
  (List.finRange ((n + 1) * 8)).map (orderEquiv n choice)

theorem path_length (n : Nat) (choice : Bool) : (path n choice).length = (n + 1) * 8 := by
  simp [path]

theorem path_nodup (n : Nat) (choice : Bool) : (path n choice).Nodup :=
  (List.nodup_finRange _).map (orderEquiv n choice).injective

theorem mem_path (n : Nat) (choice : Bool) (v : Vertex n) : v ∈ path n choice := by
  obtain ⟨i, rfl⟩ := (orderEquiv n choice).surjective v
  simp [path]

theorem path_chain {n : Nat} {choice : Bool} {R : Vertex n → Vertex n → Prop}
    (h : (cover n choice).InternalEdges R) : (path n choice).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i < pathSize n := by rw [path_length] at hi; unfold pathSize; omega
  have hh := h () ⟨i, hi'⟩
  have hib : i + 1 < (n + 1) * 8 := by simpa only [path_length] using hi
  have hia : i < (n + 1) * 8 := by omega
  change R (orderEquiv n choice ⟨i, hia⟩) (orderEquiv n choice ⟨i + 1, hib⟩) at hh
  simpa [path] using hh

theorem path_adjacent (n : Nat) (choice : Bool) : (path n choice).IsChain (Adj n) :=
  path_chain (cover_adjacent n choice)

theorem path_classification {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ choice : Bool, (path n choice).IsChain (fun u v => succ (embed u) = embed v) := by
  obtain ⟨choice, hc⟩ := route_classification succ ho embed he hg
  exact ⟨choice, path_chain hc⟩

end GridHardness.XorWire
