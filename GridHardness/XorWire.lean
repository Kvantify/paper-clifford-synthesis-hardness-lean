/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorRouting

/-!
# XOR Wire

An XOR wire with any positive number of serial sections. Its two
directions are coupled by ordinary graph edges, and the route chosen in one
section is forced throughout the wire by a global Hamiltonian permutation.
-/

@[expose] public section

namespace GridHardness.XorWire

abbrev Vertex (n : Nat) := Fin (n + 1) × Fin 8

def Adj (n : Nat) (u v : Vertex n) : Prop :=
  (u.1 = v.1 ∧ ∃ e : Fin 10, XorGadget.arc e = (u.2, v.2)) ∨
  (u.1.val + 1 = v.1.val ∧ u.2 = 0 ∧ v.2 = 3) ∨
  (v.1.val + 1 = u.1.val ∧ u.2 = 7 ∧ v.2 = 4)

instance (n : Nat) : DecidableRel (Adj n) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def entry (n : Nat) (choice : Bool) : Vertex n :=
  if choice then (0, 3) else (Fin.last n, 4)

def exit (n : Nat) (choice : Bool) : Vertex n :=
  if choice then (Fin.last n, 0) else (0, 7)

def route (choice : Bool) : XorGadget.Selection :=
  if choice then XorGadget.leftRoute else XorGadget.rightRoute

structure Isolated {V : Type*} (n : Nat) (succ : V → V)
    (embed : Vertex n → V) : Prop where
  internal : ∀ u v, succ (embed u) = embed v → Adj n u v
  outgoing : ∀ u, u ≠ exit n true → u ≠ exit n false →
    ∃ v, succ (embed u) = embed v
  incoming : ∀ v, v ≠ entry n true → v ≠ entry n false →
    ∃ u, succ (embed u) = embed v

theorem component_selection {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) (i : Fin (n + 1)) :
    PlanarSatXor.selection succ (fun j => embed (i, j)) = XorGadget.leftRoute ∨
      PlanarSatXor.selection succ (fun j => embed (i, j)) = XorGadget.rightRoute := by
  have hi : Function.Injective (fun j => embed (i, j)) :=
    fun _ _ h => congrArg Prod.snd (he h)
  have hd : XorGadget.DegreeOK (PlanarSatXor.selection succ (fun j => embed (i, j))) := by
    apply PlanarSatXor.degree_of_isolation succ _ hi
    · intro j hj0 hj7
      obtain ⟨⟨k, l⟩, hs⟩ := hg.outgoing (i, j)
        (fun h => hj0 (congrArg Prod.snd h)) (fun h => hj7 (congrArg Prod.snd h))
      rcases hg.internal _ _ hs with ⟨hik, e, ha⟩ | ⟨_, hj, _⟩ | ⟨_, hj, _⟩
      · dsimp at hik ha
        subst k
        exact ⟨e, congrArg Prod.fst ha, by simpa [ha] using hs⟩
      · exact False.elim (hj0 hj)
      · exact False.elim (hj7 hj)
    · intro j hj3 hj4
      obtain ⟨⟨k, l⟩, hs⟩ := hg.incoming (i, j)
        (fun h => hj3 (congrArg Prod.snd h)) (fun h => hj4 (congrArg Prod.snd h))
      rcases hg.internal _ _ hs with ⟨hki, e, ha⟩ | ⟨_, _, hj⟩ | ⟨_, _, hj⟩
      · dsimp at hki ha
        subst k
        exact ⟨e, congrArg Prod.snd ha, by simpa [ha] using hs⟩
      · exact False.elim (hj3 hj)
      · exact False.elim (hj4 hj)
  exact XorGadget.selection_of_oneOrbit_injective succ ho _ hi _ hd
    (fun e hb => (PlanarSatXor.selection_true _ _ _).mp hb)

theorem zero_outgoing {n : Nat} (i : Fin n) (v : Vertex n)
    (h : Adj n (i.castSucc, 0) v) :
    v = (i.castSucc, 1) ∨ v = (i.succ, 3) := by
  rcases v with ⟨k, j⟩
  rcases h with ⟨hk, e, ha⟩ | ⟨hk, _, hj⟩ | ⟨_, hn, _⟩
  · dsimp at hk ha
    subst k
    have hh : ∀ e : Fin 10, (XorGadget.arc e).1 = 0 → (XorGadget.arc e).2 = 1 := by decide
    exact Or.inl (Prod.ext rfl ((congrArg Prod.snd ha).symm.trans
      (hh e (congrArg Prod.fst ha))))
  · exact Or.inr (Prod.ext (Fin.ext (by simpa using hk.symm)) hj)
  · simp at hn

theorem seven_outgoing {n : Nat} (i : Fin n) (v : Vertex n)
    (h : Adj n (i.succ, 7) v) :
    v = (i.succ, 6) ∨ v = (i.castSucc, 4) := by
  rcases v with ⟨k, j⟩
  rcases h with ⟨hk, e, ha⟩ | ⟨_, hn, _⟩ | ⟨hk, _, hj⟩
  · dsimp at hk ha
    subst k
    have hh : ∀ e : Fin 10, (XorGadget.arc e).1 = 7 → (XorGadget.arc e).2 = 6 := by decide
    exact Or.inl (Prod.ext rfl ((congrArg Prod.snd ha).symm.trans
      (hh e (congrArg Prod.fst ha))))
  · simp at hn
  · exact Or.inr (Prod.ext (Fin.ext (by dsimp at hk ⊢; omega)) hj)

theorem three_incoming {n : Nat} (i : Fin n) (u : Vertex n)
    (h : Adj n u (i.succ, 3)) :
    u = (i.succ, 2) ∨ u = (i.castSucc, 0) := by
  rcases u with ⟨k, j⟩
  rcases h with ⟨hk, e, ha⟩ | ⟨hk, hj, _⟩ | ⟨_, _, hn⟩
  · dsimp at hk ha
    subst k
    have hh : ∀ e : Fin 10, (XorGadget.arc e).2 = 3 → (XorGadget.arc e).1 = 2 := by decide
    exact Or.inl (Prod.ext rfl ((congrArg Prod.fst ha).symm.trans
      (hh e (congrArg Prod.snd ha))))
  · exact Or.inr (Prod.ext (Fin.ext (by dsimp at hk ⊢; omega)) hj)
  · simp at hn

theorem adjacent_equal {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) (i : Fin n) :
    PlanarSatXor.selection succ (fun j => embed (i.castSucc, j)) =
      PlanarSatXor.selection succ (fun j => embed (i.succ, j)) := by
  have ha := component_selection succ ho embed he hg i.castSucc
  have hb := component_selection succ ho embed he hg i.succ
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ha.trans hb.symm
  · obtain ⟨v, hv⟩ := hg.outgoing (i.castSucc, 0)
      (by intro h; have hh := congrArg (fun w : Vertex n => w.1.val) h
          simp [exit] at hh; have := i.isLt; omega)
      (by simp [exit])
    rcases zero_outgoing i v (hg.internal _ _ hv) with rfl | rfl
    · have hh := (PlanarSatXor.selection_true succ (fun j => embed (i.castSucc, j)) 0).mpr hv
      rw [ha] at hh
      contradiction
    · have hs : succ (embed (i.succ, 2)) = embed (i.succ, 3) := by
        apply (PlanarSatXor.selection_true succ (fun j => embed (i.succ, j)) 3).mp
        rw [hb]; rfl
      have hh := congrArg Prod.snd (he (succ.injective (hv.trans hs.symm)))
      simp at hh
  · obtain ⟨u, hu⟩ := hg.incoming (i.succ, 3)
      (by intro h; have hh := congrArg (fun w : Vertex n => w.1.val) h
          simp [entry] at hh)
      (by simp [entry])
    rcases three_incoming i u (hg.internal _ _ hu) with rfl | rfl
    · have hh := (PlanarSatXor.selection_true succ (fun j => embed (i.succ, j)) 3).mpr hu
      rw [hb] at hh
      contradiction
    · have hs : succ (embed (i.castSucc, 0)) = embed (i.castSucc, 1) := by
        apply (PlanarSatXor.selection_true succ (fun j => embed (i.castSucc, j)) 0).mp
        rw [ha]; rfl
      have hh := congrArg Prod.snd (he (hu.symm.trans hs))
      simp at hh
  · exact ha.trans hb.symm

theorem uniform_selection {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (ho : OneOrbit succ) (embed : Vertex n → V)
    (he : Function.Injective embed) (hg : Isolated n succ embed) :
    ∃ choice : Bool, ∀ i : Fin (n + 1),
      PlanarSatXor.selection succ (fun j => embed (i, j)) = route choice := by
  have hall : ∀ i : Fin (n + 1),
      PlanarSatXor.selection succ (fun j => embed (i, j)) =
        PlanarSatXor.selection succ (fun j => embed (0, j)) := by
    apply Fin.induction
    · rfl
    · intro i hi
      exact (adjacent_equal succ ho embed he hg i).symm.trans hi
  rcases component_selection succ ho embed he hg 0 with h | h
  · exact ⟨true, fun i => (hall i).trans h⟩
  · exact ⟨false, fun i => (hall i).trans h⟩

theorem forward_link {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (embed : Vertex n → V) (hg : Isolated n succ embed)
    (i : Fin n)
    (hi : PlanarSatXor.selection succ (fun j => embed (i.castSucc, j)) = route true) :
    succ (embed (i.castSucc, 0)) = embed (i.succ, 3) := by
  obtain ⟨v, hv⟩ := hg.outgoing (i.castSucc, 0)
    (by intro h; have hh := congrArg (fun w : Vertex n => w.1.val) h
        simp [exit] at hh; have := i.isLt; omega)
    (by simp [exit])
  rcases zero_outgoing i v (hg.internal _ _ hv) with rfl | rfl
  · have hh := (PlanarSatXor.selection_true succ (fun j => embed (i.castSucc, j)) 0).mpr hv
    rw [hi] at hh
    contradiction
  · exact hv

theorem reverse_link {n : Nat} {V : Type*} [DecidableEq V]
    (succ : Equiv.Perm V) (embed : Vertex n → V) (hg : Isolated n succ embed)
    (i : Fin n)
    (hi : PlanarSatXor.selection succ (fun j => embed (i.succ, j)) = route false) :
    succ (embed (i.succ, 7)) = embed (i.castSucc, 4) := by
  obtain ⟨v, hv⟩ := hg.outgoing (i.succ, 7)
    (by simp [exit])
    (by intro h; have hh := congrArg (fun w : Vertex n => w.1.val) h
        simp [exit] at hh)
  rcases seven_outgoing i v (hg.internal _ _ hv) with rfl | rfl
  · have hh := (PlanarSatXor.selection_true succ (fun j => embed (i.succ, j)) 9).mpr hv
    rw [hi] at hh
    contradiction
  · exact hv

end GridHardness.XorWire
