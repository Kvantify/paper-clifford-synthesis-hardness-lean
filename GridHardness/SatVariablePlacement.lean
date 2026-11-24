/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableLattice
public import GridHardness.SatVariableOrderFinite

/-!
# SAT Variable Placement

Simultaneous variable-body vertices to the right of the occurrence
wires. Only the last variable block may be empty. This condition is
derived from the encoded SAT variable list for every width-three input.
-/

@[expose] public section

namespace GridHardness.SatVariablePlacement
open PlanarSatAssembly SatVariableOrder SatVariableLattice
set_option autoImplicit false

variable {n m : Nat}

abbrev Vertex (n : Nat) := Fin n × Bool

def Regular (φ : Formula n m) : Prop :=
  ∀ v, count φ v=0 → v.val+1=n

def point (φ : Formula n m) (v : Fin n) : Bool → Point
  | false => entry (3*m) (SatVariableOrder.prefix φ v)
  | true => if count φ v=0 then emptyExit (3*m) (SatVariableOrder.prefix φ v)
      else exit (3*m) (SatVariableOrder.prefix φ v+count φ v)

def vertexPoint (φ : Formula n m) (z : Vertex n) : Point := point φ z.1 z.2

def index (z : Vertex n) : Nat := 2*z.1.val+z.2.toNat

theorem index_injective (n : Nat) : Function.Injective (index (n:=n)) := by
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  have he : v=w := by
    apply Fin.ext
    cases a <;> cases b <;> simp [index] at h <;> omega
  subst w
  have hb : a=b := by cases a <;> cases b <;> simp_all [index]
  cases hb
  rfl

theorem finite_regular (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) : Regular (finiteFormula x) := by
  intro v hv
  have he := (SatVariableOrder.Finite.count_zero_iff_last x hw v).mp hv
  rw [he]
  rfl

theorem count_pos_before (φ : Formula n m) (hφ : Regular φ)
    (v w : Fin n) (hvw : v <w) : 0<count φ v := by
  by_contra! h
  have hn := hφ v (by omega)
  have hw := w.isLt
  have hvw' : v.val<w.val := hvw
  omega

@[simp] theorem point_x (φ : Formula n m) (v : Fin n) (b : Bool) :
    (point φ v b).1=wireX (3*m)+64 := by
  cases b <;> simp [point,entry,emptyExit,exit]
  split <;> rfl

theorem entry_lt_exit (φ : Formula n m) (v : Fin n) :
    (point φ v false).2<(point φ v true).2 := by
  unfold point
  split_ifs with h
  · dsimp [entry,emptyExit]
    omega
  · dsimp [entry,exit,entryY,exitY]
    have hp : 0<count φ v := by omega
    omega

theorem point_between (φ : Formula n m) (v : Fin n) (b : Bool) :
    (point φ v false).2≤(point φ v b).2 ∧
      (point φ v b).2≤(point φ v true).2 := by
  have h := entry_lt_exit φ v
  cases b <;> exact ⟨by omega,by omega⟩

/-- At least 64 lattice steps separate the exit of an earlier variable
from the entry of a later variable. -/
theorem exit_before_entry (φ : Formula n m) (hφ : Regular φ)
    (v w : Fin n) (hvw : v <w) :
    (point φ v true).2+64≤(point φ w false).2 := by
  have hp := count_pos_before φ hφ v w hvw
  have hb := blocks_ordered φ hvw
  simp only [point,ite_eq_right (by omega : ¬count φ v=0)]
  dsimp [exit,entry,exitY,entryY]
  omega

theorem different_variable_order (φ : Formula n m) (hφ : Regular φ)
    (v w : Fin n) (hvw : v <w) (a b : Bool) :
    (point φ v a).2<(point φ w b).2 := by
  have hv := point_between φ v a
  have hw := point_between φ w b
  have hg := exit_before_entry φ hφ v w hvw
  omega

theorem index_lt_y_lt (φ : Formula n m) (hφ : Regular φ)
    (u v : Vertex n) (h : index u < index v) :
    (vertexPoint φ u).2<(vertexPoint φ v).2 := by
  rcases u with ⟨u,a⟩
  rcases v with ⟨v,b⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · exact different_variable_order φ hφ u v huv a b
  · subst v
    have ha : a=false := by cases a <;> cases b <;> simp_all [index]
    have hb : b=true := by cases a <;> cases b <;> simp_all [index]
    subst a
    subst b
    exact entry_lt_exit φ u
  · have hv : v.val<u.val := huv
    cases a <;> cases b <;> simp [index] at h <;> omega

theorem y_le_iff (φ : Formula n m) (hφ : Regular φ) (u v : Vertex n) :
    (vertexPoint φ u).2≤(vertexPoint φ v).2 ↔ index u ≤ index v := by
  constructor
  · intro h
    by_contra! hn
    have he := index_lt_y_lt φ hφ v u hn
    omega
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact (index_lt_y_lt φ hφ u v h).le
    · have he := index_injective n h
      simp [he]

theorem point_injective (φ : Formula n m) (hφ : Regular φ) :
    Function.Injective (vertexPoint φ) := by
  intro u v he
  have hy := congrArg Prod.snd he
  apply index_injective n
  have huv := (y_le_iff φ hφ u v).mp (by omega)
  have hvu := (y_le_iff φ hφ v u).mp (by omega)
  omega

theorem point_bounds (φ : Formula n m) (v : Fin n) (b : Bool) :
    (point φ v b).1=wireX (3*m)+64 ∧
      0≤(point φ v b).2 ∧ (point φ v b).2≤512*(3*m:Int)+192 := by
  have hb := prefix_add_count_le φ v
  refine ⟨point_x φ v b,?_⟩
  cases b <;> unfold point
  · dsimp [entry,entryY]
    omega
  · split_ifs <;> dsimp [emptyExit,exit,entryY,exitY] <;> omega

end GridHardness.SatVariablePlacement
