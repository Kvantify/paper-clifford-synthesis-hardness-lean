/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleBundle
public import GridHardness.MarkedCrossoverDegree

/-!
# XOR Line Degree

Degree bounds for the actual four-row XOR-line replacement.
Boundary uniqueness is an edge condition; no Hamiltonian traversal is used.
-/

@[expose] public section

namespace GridHardness.XorLine.Degree
open XorWire.NetworkDegree (inDegree outDegree)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

variable {O W P V : Type*}

def portMap (port : P → W) : O ⊕ P → O ⊕ W
  | .inl o => .inl o
  | .inr p => .inr (port p)

theorem portMap_injective (port : P → W) (hp : Function.Injective port) :
    Function.Injective (portMap (O := O) port) := by
  rintro (o | p) (o' | p') he
  · exact congrArg Sum.inl (Sum.inl.inj he)
  · cases he
  · cases he
  · exact congrArg Sum.inr (hp (Sum.inr.inj he))

private def predecessors (outside : O → O → Prop) (leave : P → O → Prop)
    (o : O) : O ⊕ P → Prop
  | .inl u => outside u o
  | .inr p => leave p o

private def successors (outside : O → O → Prop) (enter : O → P → Prop)
    (o : O) : O ⊕ P → Prop
  | .inl u => outside o u
  | .inr p => enter o p

private theorem attached_outside_inDegree [Fintype O] [Fintype W] [Fintype P]
    (outside : O → O → Prop) (inside : W → W → Prop) (input output : P → W)
    (enter : O → P → Prop) (leave : P → O → Prop)
    (ho : Function.Injective output) (o : O) :
    by classical exact inDegree (XorLineAttachment.Adj outside inside input output enter leave) (.inl o) =
      (Finset.univ.filter (predecessors outside leave o)).card := by
  classical
  have he : Finset.univ.filter
      (fun u => XorLineAttachment.Adj outside inside input output enter leave u (.inl o)) =
      (Finset.univ.filter (predecessors outside leave o)).image (portMap output) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      cases u with
      | inl u => exact ⟨.inl u, h, rfl⟩
      | inr w =>
        obtain ⟨p, hp, hw⟩ := h
        exact ⟨.inr p, hp, congrArg Sum.inr hw.symm⟩
    · rintro ⟨u, hu, rfl⟩
      cases u with
      | inl u => exact hu
      | inr p => exact ⟨p, hu, rfl⟩
  unfold inDegree
  rw [he, Finset.card_image_of_injective _ (portMap_injective output ho)]

private theorem attached_outside_outDegree [Fintype O] [Fintype W] [Fintype P]
    (outside : O → O → Prop) (inside : W → W → Prop) (input output : P → W)
    (enter : O → P → Prop) (leave : P → O → Prop)
    (hi : Function.Injective input) (o : O) :
    by classical exact outDegree (XorLineAttachment.Adj outside inside input output enter leave) (.inl o) =
      (Finset.univ.filter (successors outside enter o)).card := by
  classical
  have he : Finset.univ.filter
      (fun u => XorLineAttachment.Adj outside inside input output enter leave (.inl o) u) =
      (Finset.univ.filter (successors outside enter o)).image (portMap input) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      cases u with
      | inl u => exact ⟨.inl u, h, rfl⟩
      | inr w =>
        obtain ⟨p, hp, hw⟩ := h
        exact ⟨.inr p, hp, congrArg Sum.inr hw.symm⟩
    · rintro ⟨u, hu, rfl⟩
      cases u with
      | inl u => exact hu
      | inr p => exact ⟨p, hu, rfl⟩
  unfold outDegree
  rw [he, Finset.card_image_of_injective _ (portMap_injective input hi)]

noncomputable instance outsideFintype [Fintype V] {n : Nat}
    (e : Source.Vertex n → V) : Fintype (Marked.Outside e) := Fintype.ofFinite _

theorem outside_inDegree_eq [Fintype V] {n : Nat}
    (D : V → V → Prop) (e : Source.Vertex n → V) (he : Function.Injective e)
    (h : Marked.Isolation D e) (o : Marked.Outside e) :
    inDegree (Marked.replacement D e) (.inl o) = inDegree D o.val := by
  classical
  have hr := MarkedCrossover.Degree.inDegree_relabel
    (Source.attached n (Marked.outside D e) (Marked.enter D e) (Marked.leave D e)) D
    (Marked.equivToOriginal e he) (fun a b => (Marked.original_adj_iff D e h a b).symm) (.inl o)
  have hs := attached_outside_inDegree (Marked.outside D e) (Source.Adj n)
    (Source.inputPort n) (Source.outputPort n) (Marked.enter D e) (Marked.leave D e)
    (Source.outputPort_injective n) o
  have ht := attached_outside_inDegree (Marked.outside D e) (Adj n)
    (inputPort n) (outputPort n) (Marked.enter D e) (Marked.leave D e)
    (outputPort_injective n) o
  exact ht.trans (hs.symm.trans hr)

theorem outside_outDegree_eq [Fintype V] {n : Nat}
    (D : V → V → Prop) (e : Source.Vertex n → V) (he : Function.Injective e)
    (h : Marked.Isolation D e) (o : Marked.Outside e) :
    outDegree (Marked.replacement D e) (.inl o) = outDegree D o.val := by
  classical
  have hr := MarkedCrossover.Degree.outDegree_relabel
    (Source.attached n (Marked.outside D e) (Marked.enter D e) (Marked.leave D e)) D
    (Marked.equivToOriginal e he) (fun a b => (Marked.original_adj_iff D e h a b).symm) (.inl o)
  have hs := attached_outside_outDegree (Marked.outside D e) (Source.Adj n)
    (Source.inputPort n) (Source.outputPort n) (Marked.enter D e) (Marked.leave D e)
    (Source.inputPort_injective n) o
  have ht := attached_outside_outDegree (Marked.outside D e) (Adj n)
    (inputPort n) (outputPort n) (Marked.enter D e) (Marked.leave D e)
    (inputPort_injective n) o
  exact ht.trans (hs.symm.trans hr)

private theorem neighbor_card_bound {A B : Type*} [Fintype A] [Fintype B]
    (R : A → Prop) (S : B → Prop) (f : B → A) (P : Prop) (extra : A)
    [DecidablePred R] [DecidablePred S] [Decidable P]
    (h : ∀ a, R a → (∃ b, S b ∧ a = f b) ∨ (P ∧ a = extra)) :
    (Finset.univ.filter R).card ≤ (Finset.univ.filter S).card + if P then 1 else 0 := by
  classical
  have hs : Finset.univ.filter R ⊆ (Finset.univ.filter S).image f ∪ if P then {extra} else ∅ := by
    intro a ha
    rcases h a (Finset.mem_filter.mp ha).2 with ⟨b, hb, rfl⟩ | ⟨hp, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩)
    · apply Finset.mem_union_right
      simp [hp]
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hi := Finset.card_image_le (s := Finset.univ.filter S) (f := f)
  have hp : (if P then ({extra} : Finset A) else ∅).card = if P then 1 else 0 := by
    split_ifs <;> simp
  omega

def localIn (v : Vertex 4) : Nat := (Finset.univ.filter (fun w => Adj 4 w v)).card
def localOut (v : Vertex 4) : Nat := (Finset.univ.filter (fun w => Adj 4 v w)).card
def entries : Finset (Vertex 4) := Finset.univ.image (inputPort 4)
def exits : Finset (Vertex 4) := Finset.univ.image (outputPort 4)

theorem augmented_degrees : ∀ v : Vertex 4,
    localIn v + (if v ∈ entries then 1 else 0) ≤ 2 ∧
    localOut v + (if v ∈ exits then 1 else 0) ≤ 2 ∧
    (localIn v + (if v ∈ entries then 1 else 0)) +
      (localOut v + (if v ∈ exits then 1 else 0)) ≤ 3 := by decide

section Local
variable (outside : O → O → Prop) (enter : O → Port 4 → Prop) (leave : Port 4 → O → Prop)

def extraIn (v : Vertex 4) (u : O ⊕ Vertex 4) : Prop :=
  ∃ p o, enter o p ∧ v = inputPort 4 p ∧ u = .inl o
def extraOut (v : Vertex 4) (u : O ⊕ Vertex 4) : Prop :=
  ∃ p o, leave p o ∧ v = outputPort 4 p ∧ u = .inl o

noncomputable def chosenIn (v : Vertex 4) : O ⊕ Vertex 4 := by
  classical
  exact if h : ∃ u, extraIn enter v u then h.choose else .inr (x 0 0)
noncomputable def chosenOut (v : Vertex 4) : O ⊕ Vertex 4 := by
  classical
  exact if h : ∃ u, extraOut leave v u then h.choose else .inr (x 0 0)

theorem extraIn_eq (hu : ∀ p a b, enter a p → enter b p → a = b)
    (v : Vertex 4) (u : O ⊕ Vertex 4) (h : extraIn enter v u) : u = chosenIn enter v := by
  classical
  unfold chosenIn
  rw [dite_eq_left ⟨u, h⟩]
  obtain ⟨p, o, hp, hv, rfl⟩ := h
  obtain ⟨q, o', hq, hv', he⟩ := Exists.choose_spec (show ∃ u, extraIn enter v u from ⟨_, ⟨p, o, hp, hv, rfl⟩⟩)
  have hpq := inputPort_injective 4 (hv.symm.trans hv')
  subst q
  exact (congrArg Sum.inl (hu p o o' hp hq)).trans he.symm

theorem extraOut_eq (hu : ∀ p a b, leave p a → leave p b → a = b)
    (v : Vertex 4) (u : O ⊕ Vertex 4) (h : extraOut leave v u) : u = chosenOut leave v := by
  classical
  unfold chosenOut
  rw [dite_eq_left ⟨u, h⟩]
  obtain ⟨p, o, hp, hv, rfl⟩ := h
  obtain ⟨q, o', hq, hv', he⟩ := Exists.choose_spec (show ∃ u, extraOut leave v u from ⟨_, ⟨p, o, hp, hv, rfl⟩⟩)
  have hpq := outputPort_injective 4 (hv.symm.trans hv')
  subst q
  exact (congrArg Sum.inl (hu p o o' hp hq)).trans he.symm

theorem cell_degree_bounds [Fintype O]
    (hin : ∀ p a b, enter a p → enter b p → a = b)
    (hout : ∀ p a b, leave p a → leave p b → a = b) (v : Vertex 4) :
    inDegree (attached 4 outside enter leave) (.inr v) ≤ 2 ∧
    outDegree (attached 4 outside enter leave) (.inr v) ≤ 2 ∧
    inDegree (attached 4 outside enter leave) (.inr v) +
      outDegree (attached 4 outside enter leave) (.inr v) ≤ 3 := by
  classical
  have hi : inDegree (attached 4 outside enter leave) (.inr v) ≤
      localIn v + if v ∈ entries then 1 else 0 := by
    unfold inDegree localIn
    apply neighbor_card_bound _ (fun w => Adj 4 w v) Sum.inr _ (chosenIn enter v)
    intro u hu
    cases u with
    | inr w => exact Or.inl ⟨w, hu, rfl⟩
    | inl o =>
      obtain ⟨p, hp, hv⟩ := hu
      exact Or.inr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hv.symm⟩,
        extraIn_eq enter hin v (.inl o) ⟨p, o, hp, hv, rfl⟩⟩
  have ho : outDegree (attached 4 outside enter leave) (.inr v) ≤
      localOut v + if v ∈ exits then 1 else 0 := by
    unfold outDegree localOut
    apply neighbor_card_bound _ (fun w => Adj 4 v w) Sum.inr _ (chosenOut leave v)
    intro u hu
    cases u with
    | inr w => exact Or.inl ⟨w, hu, rfl⟩
    | inl o =>
      obtain ⟨p, hp, hv⟩ := hu
      exact Or.inr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hv.symm⟩,
        extraOut_eq leave hout v (.inl o) ⟨p, o, hp, hv, rfl⟩⟩
  have hb := augmented_degrees v
  omega

end Local
end GridHardness.XorLine.Degree
