/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.StandardSpace

/-!
# Observation

Visible vectors on physical wires, including equality of successive visible
vectors. The local chart's observations are identified with these actual vectors.
-/

@[expose] public section

namespace CliffordSynthesis.Observation

open LinearMap (BilinForm)
open Planes (F plane SymplecticPair)
open SymplecticCircuit (Rows IsSymplectic)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

attribute [local instance] Classical.propDecidable

noncomputable def observe (W : Submodule F V) (a b : V) : Option V := by
  classical
  exact [a, b, a + b].find? (fun v => decide (v ∈ W))

def present {α : Type*} : Option α → Nat
  | none => 0
  | some _ => 1

noncomputable def birth {α : Type*} (old new : Option α) : Nat := by
  classical
  exact if new.isSome ∧ new ≠ old then 1 else 0

private theorem candidates (B : BilinForm F V) (a b : V) (h : SymplecticPair B a b)
    (v : V) : v ∈ [a, b, a + b] ↔ v ≠ 0 ∧ v ∈ plane a b := by
  have ha : a ≠ 0 := by intro hz; simpa [hz] using h.ab
  have hb : b ≠ 0 := by intro hz; simpa [hz] using h.ab
  have hab : a + b ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => B a x) hz
    simp [map_add, h.aa, h.ab] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false, Planes.mem_plane_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨ha, Or.inr (Or.inl rfl)⟩
    · exact ⟨hb, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨hab, Or.inr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨hv, hz | hv'⟩
    · exact False.elim (hv hz)
    · exact hv'

/-- A selected visible vector is exactly a nonzero member of W intersected
with the qubit plane; selection order is immaterial by isotropy. -/
theorem observe_eq_some (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b : V) (h : SymplecticPair B a b) (v : V) :
    observe W a b = some v ↔ v ≠ 0 ∧ v ∈ W ⊓ plane a b := by
  classical
  constructor
  · intro hv
    have hv' := (candidates B a b h v).mp (List.mem_of_find?_eq_some hv)
    have hvW : decide (v ∈ W) = true := List.find?_some (p := fun x => decide (x ∈ W)) hv
    exact ⟨hv'.1, of_decide_eq_true hvW, hv'.2⟩
  · rintro ⟨hv0, hvW, hvP⟩
    cases ho : observe W a b with
    | none =>
      have hn := List.find?_eq_none.mp ho v ((candidates B a b h v).mpr ⟨hv0, hvP⟩)
      exact False.elim ((by simpa using hn : v ∉ W) hvW)
    | some u =>
      have hu := (candidates B a b h u).mp (List.mem_of_find?_eq_some ho)
      have huW' : decide (u ∈ W) = true := List.find?_some (p := fun x => decide (x ∈ W)) ho
      have huW : u ∈ W := of_decide_eq_true huW'
      have he := Planes.visible_unique B W hW a b h ⟨huW, hu.2⟩ ⟨hvW, hvP⟩ hu.1 hv0
      exact congrArg some he

theorem observe_plane_invariant (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V)
    (hab : SymplecticPair B a b) (hcd : SymplecticPair B c d)
    (he : plane a b = plane c d) : observe W a b = observe W c d := by
  apply Option.ext
  intro v
  rw [observe_eq_some B W hW a b hab, observe_eq_some B W hW c d hcd, he]

private theorem present_map {α β : Type*} (f : α → β) (o : Option α) :
    present (o.map f) = present o := by cases o <;> rfl

private theorem birth_map {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (old new : Option α) : birth (old.map f) (new.map f) = birth old new := by
  classical
  cases old <;> cases new <;> simp [birth, hf.eq_iff]

private theorem local_present (o : Option Local.V) : present o = Local.present o := by
  cases o <;> rfl

private theorem local_birth (old new : Option Local.V) : birth old new = Local.birth old new := by
  classical
  cases old <;> cases new <;> simp [birth, Local.birth]

private theorem observe_chart (W : Submodule F V) (a b c d u v : V)
    (qs : List Local.V) (he : qs.map (LocalChart.chart a b c d) = [u, v, u + v]) :
    observe W u v = (qs.find? (fun q => decide (LocalChart.chart a b c d q ∈ W))).map
      (LocalChart.chart a b c d) := by
  classical
  rw [observe, ← he, List.find?_map]
  rfl

/-- All four finite observations are the actual vectors on the control and
target wires before and after their CNOT. -/
theorem chart_observations (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V) (h : LocalChart.Frame B a b c d) :
    let w := LocalChart.pullback B W hW a b c d h
    let f := LocalChart.chart a b c d
    observe W a b = w.before.1.map f ∧ observe W c d = w.before.2.map f ∧
    observe W a (b + d) = w.after.1.map f ∧
    observe W (c + a) d = w.after.2.map f := by
  classical
  dsimp only
  refine ⟨observe_chart W a b c d a b [1, 4, 5] ?_,
    observe_chart W a b c d c d [2, 8, 10] ?_,
    observe_chart W a b c d a (b + d) [1, 12, 13] ?_,
    observe_chart W a b c d (c + a) d [3, 8, 11] ?_⟩
  all_goals simp only [
    show (1 : Local.V) = (true, false, false, false) by rfl,
    show (2 : Local.V) = (false, true, false, false) by rfl,
    show (3 : Local.V) = (true, true, false, false) by rfl,
    show (4 : Local.V) = (false, false, true, false) by rfl,
    show (5 : Local.V) = (true, false, true, false) by rfl,
    show (8 : Local.V) = (false, false, false, true) by rfl,
    show (10 : Local.V) = (false, true, false, true) by rfl,
    show (11 : Local.V) = (true, true, false, true) by rfl,
    show (12 : Local.V) = (false, false, true, true) by rfl,
    show (13 : Local.V) = (true, false, true, true) by rfl,
    List.map, LocalChart.chart, LocalChart.bit]
  all_goals simp [add_comm, add_left_comm]

noncomputable def visible (W : Submodule F V) (a : Rows n V) (i : Fin n) : Option V :=
  observe W (a.x i) (a.z i)

noncomputable def count (W : Submodule F V) (a : Rows n V) : Nat :=
  ∑ i, present (visible W a i)

noncomputable def signature (W : Submodule F V) (a a' : Rows n V) (c t : Fin n) :
    Nat × Nat × Nat :=
  (present (visible W a c) + present (visible W a t),
   present (visible W a' c) + present (visible W a' t),
   birth (visible W a c) (visible W a' c) + birth (visible W a t) (visible W a' t))

theorem cnot_signature (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (c t : Fin n) (hct : c ≠ t) :
    signature W a (SymplecticCircuit.CX c t a) c t =
      (LocalChart.pullback B W hW (a.x c) (a.z c) (a.x t) (a.z t)
        (SymplecticCircuit.endpoint_frame B a ha c t hct)).signature := by
  have h := SymplecticCircuit.endpoint_frame B a ha c t hct
  have ho := chart_observations B W hW (a.x c) (a.z c) (a.x t) (a.z t) h
  have hi := LocalChart.chart_injective B (a.x c) (a.z c) (a.x t) (a.z t) h
  simp only [signature, visible, SymplecticCircuit.CX, ite_true, ite_eq_right hct,
    ite_eq_right (Ne.symm hct)]
  rw [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
  simp only [present_map, birth_map _ hi, local_present, local_birth]
  rfl

/-- The finite local table expressed using ambient vectors on actual wires. -/
theorem cnot_localTable (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (c t : Fin n) (hct : c ≠ t) :
    Local.permitted (signature W a (SymplecticCircuit.CX c t a) c t) = true := by
  rw [cnot_signature B W hW a ha c t hct]
  exact LocalChart.ambient_localTable B W hW _ _ _ _ _

private theorem wire_pair (B : BilinForm F V) (a : Rows n V) (ha : IsSymplectic B a)
    (i : Fin n) : SymplecticPair B (a.x i) (a.z i) := by
  constructor <;> simp [ha.xx, ha.xz, ha.zx, ha.zz]

/-- Having the first row in W implies that it is the visible vector. -/
theorem x_visible (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (i : Fin n) (hx : a.x i ∈ W) : visible W a i = some (a.x i) := by
  apply (observe_eq_some B W hW _ _ (wire_pair B a ha i) _).mpr
  refine ⟨?_, hx, Submodule.subset_span (by simp)⟩
  intro hz
  have hh := ha.xz i i
  simp [hz] at hh

theorem count_of_all_x (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (hx : ∀ i, a.x i ∈ W) : count W a = n := by
  simp [count, x_visible B W hW a ha _ (hx _), present]

theorem hadamard_visible (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (q i : Fin n) : visible W (SymplecticCircuit.H q a) i = visible W a i := by
  by_cases hi : i = q
  · subst i
    apply observe_plane_invariant B W hW _ _ _ _
      (wire_pair B _ (SymplecticCircuit.H_symplectic B a ha q) q) (wire_pair B a ha q)
    simp [SymplecticCircuit.H, Planes.hadamard_plane]
  · simp [visible, SymplecticCircuit.H, hi]

theorem phase_visible (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (q i : Fin n) : visible W (SymplecticCircuit.S q a) i = visible W a i := by
  by_cases hi : i = q
  · subst i
    apply observe_plane_invariant B W hW _ _ _ _
      (wire_pair B _ (SymplecticCircuit.S_symplectic B a ha q) q) (wire_pair B a ha q)
    simp [SymplecticCircuit.S, Planes.phase_plane]
  · simp [visible, SymplecticCircuit.S, hi]

theorem cnot_untouched (W : Submodule F V) (a : Rows n V) (c t i : Fin n)
    (hic : i ≠ c) (hit : i ≠ t) : visible W (SymplecticCircuit.CX c t a) i = visible W a i := by
  simp [visible, SymplecticCircuit.CX, hic, hit]

private theorem sum_two (f : Fin n → Nat) (c t : Fin n) (hct : c ≠ t) :
    ∑ i, f i = (∑ i ∈ (Finset.univ.erase c).erase t, f i) + f c + f t := by
  have hc := Finset.sum_erase_add Finset.univ f (Finset.mem_univ c)
  have ht := Finset.sum_erase_add (Finset.univ.erase c) f
    (show t ∈ Finset.univ.erase c by simp [Ne.symm hct])
  omega

/-- The same untouched-wire count applies on both sides of a paid gate. -/
theorem cnot_counts (W : Submodule F V) (a : Rows n V) (c t : Fin n) (hct : c ≠ t) :
    ∃ untouched : Nat,
      count W a = untouched + (signature W a (SymplecticCircuit.CX c t a) c t).1 ∧
      count W (SymplecticCircuit.CX c t a) =
        untouched + (signature W a (SymplecticCircuit.CX c t a) c t).2.1 := by
  refine ⟨∑ i ∈ (Finset.univ.erase c).erase t, present (visible W a i), ?_, ?_⟩
  · exact (sum_two _ c t hct).trans (Nat.add_assoc _ _ _)
  · rw [count, sum_two _ c t hct]
    have he : (∑ i ∈ (Finset.univ.erase c).erase t,
        present (visible W (SymplecticCircuit.CX c t a) i)) =
        ∑ i ∈ (Finset.univ.erase c).erase t, present (visible W a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit := (Finset.mem_erase.mp hi).1
      have hic := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [cnot_untouched W a c t i hic hit]
    rw [he]
    exact Nat.add_assoc _ _ _

noncomputable def stepBirths (W : Submodule F V) (a a' : Rows n V) : Nat :=
  ∑ i, birth (visible W a i) (visible W a' i)

theorem hadamard_births (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a) (q : Fin n) :
    stepBirths W a (SymplecticCircuit.H q a) = 0 := by
  simp [stepBirths, hadamard_visible B W hW a ha, birth]

theorem phase_births (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a) (q : Fin n) :
    stepBirths W a (SymplecticCircuit.S q a) = 0 := by
  simp [stepBirths, phase_visible B W hW a ha, birth]

theorem cnot_births (W : Submodule F V) (a : Rows n V) (c t : Fin n) (hct : c ≠ t) :
    stepBirths W a (SymplecticCircuit.CX c t a) =
      (signature W a (SymplecticCircuit.CX c t a) c t).2.2 := by
  rw [stepBirths, sum_two _ c t hct]
  have he : (∑ i ∈ (Finset.univ.erase c).erase t,
      birth (visible W a i) (visible W (SymplecticCircuit.CX c t a) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hit := (Finset.mem_erase.mp hi).1
    have hic := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [cnot_untouched W a c t i hic hit, birth]
  rw [he, zero_add]
  rfl

private theorem local_row_witness (old new : Option Local.V × Option Local.V)
    (h : Local.rowAddition old new = true) :
    ∃ u v, old = (some u, some v) ∧
      (new = (some u, some (Local.add u v)) ∨ new = (some (Local.add u v), some v)) := by
  rcases old with ⟨o₁, o₂⟩
  rcases new with ⟨n₁, n₂⟩
  cases o₁ with
  | none => simp [Local.rowAddition] at h
  | some u =>
    cases o₂ with
    | none => simp [Local.rowAddition] at h
    | some v =>
      cases n₁ with
      | none => simp [Local.rowAddition] at h
      | some u' =>
        cases n₂ with
        | none => simp [Local.rowAddition] at h
        | some v' =>
          simp only [Local.rowAddition, Option.any_some, Bool.or_eq_true,
            Bool.and_eq_true, beq_iff_eq] at h
          refine ⟨u, v, rfl, ?_⟩
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr rfl

/-- A T event performs one row addition on the actual visible vectors, with
the orientation allowed to differ from the physical CNOT orientation. -/
theorem cnot_rowAddition (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (c t : Fin n) (hct : c ≠ t)
    (hs : signature W a (SymplecticCircuit.CX c t a) c t = (2, 2, 1)) :
    ∃ u v, visible W a c = some u ∧ visible W a t = some v ∧
      ((visible W (SymplecticCircuit.CX c t a) c = some u ∧
          visible W (SymplecticCircuit.CX c t a) t = some (u + v)) ∨
       (visible W (SymplecticCircuit.CX c t a) c = some (u + v) ∧
          visible W (SymplecticCircuit.CX c t a) t = some v)) := by
  rw [cnot_signature B W hW a ha c t hct] at hs
  have h := SymplecticCircuit.endpoint_frame B a ha c t hct
  have hr := LocalChart.ambient_rowAddition B W hW (a.x c) (a.z c) (a.x t) (a.z t) h hs
  obtain ⟨u, v, ho, hn⟩ := local_row_witness _ _ hr
  have hv := chart_observations B W hW (a.x c) (a.z c) (a.x t) (a.z t) h
  dsimp only at hv
  have ho₁ := congrArg Prod.fst ho
  have ho₂ := congrArg Prod.snd ho
  simp only [visible, SymplecticCircuit.CX, ite_true, ite_eq_right hct, ite_eq_right (Ne.symm hct)]
  rw [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ho₁, ho₂]
  refine ⟨LocalChart.chart (a.x c) (a.z c) (a.x t) (a.z t) u,
    LocalChart.chart (a.x c) (a.z c) (a.x t) (a.z t) v, rfl, rfl, ?_⟩
  rcases hn with hn | hn
  · left
    rw [show (LocalChart.pullback B W hW (a.x c) (a.z c) (a.x t) (a.z t) h).after.1 = some u
      from congrArg Prod.fst hn,
      show (LocalChart.pullback B W hW (a.x c) (a.z c) (a.x t) (a.z t) h).after.2 = some (Local.add u v)
      from congrArg Prod.snd hn]
    simp [LocalChart.chart_add]
  · right
    rw [show (LocalChart.pullback B W hW (a.x c) (a.z c) (a.x t) (a.z t) h).after.1 = some (Local.add u v)
      from congrArg Prod.fst hn,
      show (LocalChart.pullback B W hW (a.x c) (a.z c) (a.x t) (a.z t) h).after.2 = some v
      from congrArg Prod.snd hn]
    simp [LocalChart.chart_add]

end CliffordSynthesis.Observation
