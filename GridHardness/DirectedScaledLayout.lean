/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedLocalLayout

/-!
# Directed Scaled Layout

Place the four-vertex directed-to-bipartite gadgets around distinct
integer anchors at scale sixteen. All different gadgets have distance at
least ten. This controls the vertex neighborhoods; the external connecting
routes and the later cluster/tentacle assembly are separate constructions.
-/

@[expose] public section

namespace GridHardness.DirectedScaledLayout
open CliffordSynthesis DirectedLocalLayout
set_option autoImplicit false

abbrev Point := Int × Int

def anchor (p : Point) : Point := (16*p.1,16*p.2)

def place (p : Point) (d : Fin 4) (incoming : Bool) (i : Fin 4) : Point :=
  ((anchor p).1+(vertexPoint d incoming i).1,
   (anchor p).2+(vertexPoint d incoming i).2)

theorem translate_distance (p q r : Point) :
    IntegerGrid.manhattan (p.1+q.1,p.2+q.2) (p.1+r.1,p.2+r.2)=
      IntegerGrid.manhattan q r := by
  simp [IntegerGrid.manhattan]

theorem anchor_distance (p q : Point) :
    IntegerGrid.manhattan (anchor p) (anchor q)=16*IntegerGrid.manhattan p q := by
  dsimp [anchor,IntegerGrid.manhattan]
  rw [← mul_sub,← mul_sub]
  simp [Int.natAbs_mul,Nat.mul_add]

theorem local_radius (d : Fin 4) (incoming : Bool) (i : Fin 4) :
    IntegerGrid.manhattan (0,0) (vertexPoint d incoming i)≤3 := by
  have hi := i.isLt
  fin_cases d <;> cases incoming <;>
    simp [IntegerGrid.manhattan,vertexPoint,ray] <;> omega

theorem distance_to_anchor (p : Point) (d : Fin 4) (incoming : Bool) (i : Fin 4) :
    IntegerGrid.manhattan (anchor p) (place p d incoming i)≤3 := by
  have h := translate_distance (anchor p) (0,0) (vertexPoint d incoming i)
  simpa only [Int.add_zero,place] using h.le.trans (local_radius d incoming i)

theorem distinct_gadgets_separated (p q : Point) (hpq : p ≠q)
    (d e : Fin 4) (incoming outgoing : Bool) (i j : Fin 4) :
    10≤IntegerGrid.manhattan (place p d incoming i) (place q e outgoing j) := by
  have hp := distance_to_anchor p d incoming i
  have hq := distance_to_anchor q e outgoing j
  have h1 := IntegerGrid.manhattan_triangle (anchor p) (place p d incoming i) (anchor q)
  have h2 := IntegerGrid.manhattan_triangle (place p d incoming i)
    (place q e outgoing j) (anchor q)
  rw [IntegerGrid.manhattan_comm (place q e outgoing j) (anchor q)] at h2
  rw [anchor_distance] at h1
  have hpos : 0<IntegerGrid.manhattan p q := by
    dsimp [IntegerGrid.manhattan]
    have hne : p.1≠q.1 ∨ p.2≠q.2 := by
      by_contra h
      push Not at h
      exact hpq (Prod.ext h.1 h.2)
    omega
  omega

theorem local_injective (p : Point) (d : Fin 4) (incoming : Bool) :
    Function.Injective (place p d incoming) := by
  intro i j h
  apply vertexPoint_injective d incoming
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> dsimp [place] at hx hy ⊢ <;> omega

theorem local_adjacency (p : Point) (d : Fin 4) (incoming : Bool) (i j : Fin 4) :
    IntegerGrid.manhattan (place p d incoming i) (place p d incoming j)=1 ↔
      i.val+1=j.val ∨ j.val+1=i.val := by
  rw [place,place,translate_distance,vertexPoint_adjacent_iff]

variable {V : Type*} (point : V → Point) (direction : V → Fin 4) (incoming : V → Bool)

def vertex (v : V × Fin 4) : Point :=
  place (point v.1) (direction v.1) (incoming v.1) v.2

theorem vertex_injective (hp : Function.Injective point) :
    Function.Injective (vertex point direction incoming) := by
  rintro ⟨u,i⟩ ⟨v,j⟩ h
  have huv : u=v := by
    by_contra hn
    have hsep := distinct_gadgets_separated (point u) (point v) (fun he => hn (hp he))
      (direction u) (direction v) (incoming u) (incoming v) i j
    change 10≤IntegerGrid.manhattan (vertex point direction incoming (u,i))
      (vertex point direction incoming (v,j)) at hsep
    rw [h] at hsep
    simp [IntegerGrid.manhattan] at hsep
  subst v
  exact Prod.ext rfl (local_injective (point u) (direction u) (incoming u) h)

/-- The placed gadget vertices have precisely the internal path edges.
External graph arcs will be drawn by paths between these gadgets. -/
theorem vertex_adjacency_iff (hp : Function.Injective point) (u v : V × Fin 4) :
    IntegerGrid.manhattan (vertex point direction incoming u)
      (vertex point direction incoming v)=1 ↔
      u.1=v.1 ∧ (u.2.val+1=v.2.val ∨ v.2.val+1=u.2.val) := by
  rcases u with ⟨u,i⟩
  rcases v with ⟨v,j⟩
  by_cases huv : u=v
  · subst v
    simpa only [vertex,true_and] using local_adjacency (point u) (direction u) (incoming u) i j
  · have hsep := distinct_gadgets_separated (point u) (point v) (fun he => huv (hp he))
      (direction u) (direction v) (incoming u) (incoming v) i j
    change 10≤IntegerGrid.manhattan (vertex point direction incoming (u,i))
      (vertex point direction incoming (v,j)) at hsep
    change _ ↔ u=v ∧ _
    simp only [huv,false_and,iff_false]
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide) hsep)

theorem place_bounds (p : Point) (d : Fin 4) (incoming : Bool) (i : Fin 4) :
    16*p.1-3≤(place p d incoming i).1 ∧ (place p d incoming i).1≤16*p.1+3 ∧
    16*p.2-3≤(place p d incoming i).2 ∧ (place p d incoming i).2≤16*p.2+3 := by
  have h := distance_to_anchor p d incoming i
  dsimp [IntegerGrid.manhattan,anchor] at h
  omega

end GridHardness.DirectedScaledLayout
