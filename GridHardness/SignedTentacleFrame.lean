/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrthogonalTentacleReturn

/-!
# Signed Tentacle Frame

All signed orthogonal placements of a width-two lattice strip.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def sign (negative : Bool) (z : Int) : Int := if negative then -z else z

structure Frame where
  horizontal : Bool
  reverseX : Bool
  reverseY : Bool
  origin : Point
  deriving DecidableEq

def Frame.map (f : Frame) (p : Point) : Point :=
  place f.horizontal f.origin (sign f.reverseX p.1, sign f.reverseY p.2)

def Frame.unmap (f : Frame) (p : Point) : Point :=
  let q := if f.horizontal then (p.1 - f.origin.1, p.2 - f.origin.2)
    else (p.2 - f.origin.2, p.1 - f.origin.1)
  (sign f.reverseX q.1, sign f.reverseY q.2)

theorem Frame.unmap_map (f : Frame) (p : Point) : f.unmap (f.map p) = p := by
  rcases f with ⟨h, x, y, o⟩
  cases h <;> cases x <;> cases y <;> simp [Frame.map, Frame.unmap, place, sign]

theorem Frame.map_unmap (f : Frame) (p : Point) : f.map (f.unmap p) = p := by
  rcases f with ⟨h, x, y, o⟩
  cases h <;> cases x <;> cases y <;> apply Prod.ext <;>
    simp [Frame.map, Frame.unmap, place, sign]

def Frame.equiv (f : Frame) : Point ≃ Point where
  toFun := f.map
  invFun := f.unmap
  left_inv := f.unmap_map
  right_inv := f.map_unmap

theorem Frame.injective (f : Frame) : Function.Injective f.map := f.equiv.injective

theorem Frame.distance (f : Frame) (p q : Point) :
    IntegerGrid.manhattan (f.map p) (f.map q) = IntegerGrid.manhattan p q := by
  rw [Frame.map, Frame.map, place_distance]
  rcases f with ⟨h, x, y, o⟩
  cases x <;> cases y <;> simp [sign, IntegerGrid.manhattan] <;> omega

theorem Frame.color_eq_iff (f : Frame) (p q : Point) :
    color (f.map p) = color (f.map q) ↔ color p = color q := by
  rcases f with ⟨h, x, y, o⟩
  cases h <;> cases x <;> cases y <;>
    simp only [Frame.map, place, sign, Bool.false_eq_true, ite_false, ite_true, color] <;> omega

def Frame.hom (f : Frame) : lattice →g lattice where
  toFun := f.map
  map_rel' := by
    intro p q hp
    change IntegerGrid.manhattan _ _ = 1
    rw [f.distance]
    exact hp

theorem Frame.route (f : Frame) {S : Finset Point} {a b : Point} (h : HasRoute S a b) :
    HasRoute (S.image f.map) (f.map a) (f.map b) := by
  obtain ⟨p, hp, hc⟩ := h
  refine ⟨p.map f.hom, hp.map f.injective, ?_⟩
  intro v
  simp only [Walk.support_map, List.mem_map, Finset.mem_image]
  exact exists_congr (fun w => and_congr_left (fun _ => hc w))

theorem Frame.terminal (f : Frame) {S : Finset Point} {a b : Point} (h : TerminalPair S a b) :
    TerminalPair (S.image f.map) (f.map a) (f.map b) := by
  refine ⟨Finset.mem_image.mpr ⟨a, h.1, rfl⟩,
    Finset.mem_image.mpr ⟨b, h.2.1, rfl⟩, f.hom.map_adj h.2.2.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := h.2.2.2.1
    refine ⟨f.map x, ?_⟩
    intro v hv ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have ha' : lattice.Adj a w := by
      change IntegerGrid.manhattan _ _ = 1 at ha ⊢
      rwa [f.distance] at ha
    exact (hx w hw ha').imp (congrArg f.map) (congrArg f.map)
  · obtain ⟨x, hx⟩ := h.2.2.2.2
    refine ⟨f.map x, ?_⟩
    intro v hv ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have ha' : lattice.Adj b w := by
      change IntegerGrid.manhattan _ _ = 1 at ha ⊢
      rwa [f.distance] at ha
    exact (hx w hw ha').imp (congrArg f.map) (congrArg f.map)

def strip (f : Frame) (n : Nat) : Finset Point := (rect true (0, 0) n).image f.map

def near (f : Frame) (r : Fin 2) : Point := f.map (0, (r.val : Int))
def join (f : Frame) (r : Fin 2) : Point := f.map ((r.val : Int), 0)
def far (f : Frame) (n : Nat) (r : Fin 2) : Point := f.map ((n : Int), (r.val : Int))

theorem mem_strip_iff (f : Frame) (n : Nat) (p : Point) : p ∈ strip f n ↔
    0 ≤ (f.unmap p).1 ∧ (f.unmap p).1 ≤ n ∧
      0 ≤ (f.unmap p).2 ∧ (f.unmap p).2 ≤ 1 := by
  have hm : p ∈ strip f n ↔ f.unmap p ∈ rect true (0, 0) n := by
    constructor
    · rintro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simpa only [f.unmap_map] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨f.unmap p, hp, f.map_unmap p⟩
  rw [hm, OrthogonalTentacle.mem_rect_iff]
  simp [InRect]

theorem near_mem (f : Frame) (n : Nat) (r : Fin 2) : near f r ∈ strip f n := by
  apply Finset.mem_image.mpr
  exact ⟨_, by simpa [place] using near_mem_rect true (0, 0) n r, rfl⟩

theorem join_mem (f : Frame) (n : Nat) (hn : 1 ≤ n) (r : Fin 2) : join f r ∈ strip f n := by
  apply Finset.mem_image.mpr
  refine ⟨_, ?_, rfl⟩
  rw [OrthogonalTentacle.mem_rect_iff]
  have := r.is_lt
  dsimp [InRect]
  omega

theorem far_mem (f : Frame) (n : Nat) (r : Fin 2) : far f n r ∈ strip f n := by
  apply Finset.mem_image.mpr
  exact ⟨_, by simpa [OrthogonalTentacle.far, place] using far_mem_rect true (0, 0) n r, rfl⟩

theorem near_ne (f : Frame) : near f 0 ≠ near f 1 := by
  intro h
  have := f.injective h
  simp at this

theorem join_ne (f : Frame) : join f 0 ≠ join f 1 := by
  intro h
  have := f.injective h
  simp at this

theorem far_ne (f : Frame) (n : Nat) : far f n 0 ≠ far f n 1 := by
  intro h
  have := f.injective h
  simp at this

theorem far_join_ne (f : Frame) (n : Nat) (hn : 2 ≤ n) (r s : Fin 2) :
    far f n r ≠ join f s := by
  intro h
  have he := congrArg Prod.fst (f.injective h)
  have := s.is_lt
  dsimp at he
  omega

theorem far_near_ne (f : Frame) (n : Nat) (hn : 1 ≤ n) (r s : Fin 2) :
    far f n r ≠ near f s := by
  intro h
  have he := congrArg Prod.fst (f.injective h)
  dsimp at he
  omega

theorem strip_far_terminal (f : Frame) (n : Nat) (hn : 1 ≤ n) :
    TerminalPair (strip f n) (far f n 0) (far f n 1) := by
  have ht := f.terminal (rect_terminal true (0, 0) n hn)
  simpa [strip, far, OrthogonalTentacle.far, place] using ht

theorem strip_near_terminal (f : Frame) (n : Nat) :
    TerminalPair (strip f n) (near f 0) (near f 1) := by
  apply f.terminal
  refine ⟨?_, ?_, ?_, ⟨(1, 0), ?_⟩, ⟨(1, 1), ?_⟩⟩
  · simpa [place] using near_mem_rect true (0, 0) n 0
  · simpa [place] using near_mem_rect true (0, 0) n 1
  · change IntegerGrid.manhattan (0, 0) (0, 1) = 1
    decide
  all_goals
    intro p hp ha
    have hm := (OrthogonalTentacle.mem_rect_iff true (0, 0) n p).mp hp
    change IntegerGrid.manhattan _ _ = 1 at ha
    rw [manhattan_one_iff] at ha
    rcases p with ⟨x, y⟩
    simp only [InRect, ite_true, Prod.mk.injEq] at hm ha ⊢
    omega

theorem strip_cross (f : Frame) (n : Nat) (r t : Fin 2)
    (hc : color (near f r) ≠ color (far f n t)) :
    HasRoute (strip f n) (near f r) (far f n t) := by
  have hc' : color (0, (r.val : Int)) ≠ color ((n : Int), (t.val : Int)) :=
    fun h => hc ((f.color_eq_iff _ _).mpr h)
  have h := rect_cross_between true (0, 0) n r t (by simpa [place, OrthogonalTentacle.far] using hc')
  simpa [strip, near, far, place, OrthogonalTentacle.far] using f.route h

theorem strip_join_cross (f : Frame) (n : Nat) (hn : 1 ≤ n) (r t : Fin 2)
    (hc : color (join f r) ≠ color (far f n t)) :
    HasRoute (strip f n) (join f r) (far f n t) := by
  have hc' : color ((r.val : Int), 0) ≠ color ((n : Int), (t.val : Int)) :=
    fun h => hc ((f.color_eq_iff _ _).mpr h)
  fin_cases r
  · have h := rect_corner_cross true (0, 0) n t (by simpa [place, OrthogonalTentacle.far] using hc')
    simpa [strip, join, far, place, OrthogonalTentacle.far] using f.route h
  · have h := rect_offset_cross true (0, 0) n hn t (by simpa [place, OrthogonalTentacle.far] using hc')
    simpa [strip, join, far, place, OrthogonalTentacle.far] using f.route h

theorem strip_far_return (f : Frame) (n : Nat) :
    HasRoute (strip f n) (far f n 0) (far f n 1) := by
  simpa [strip, far, place, OrthogonalTentacle.far] using f.route (rect_far_return true (0, 0) n)

theorem strip_card (f : Frame) (n : Nat) : (strip f n).card = 2 * (n + 1) := by
  rw [strip, Finset.card_image_of_injective _ f.injective, rect_card]

end GridHardness.SignedTentacle
