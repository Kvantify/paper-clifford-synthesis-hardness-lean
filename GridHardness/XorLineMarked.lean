/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineReplacement
public import GridHardness.HamiltonianRelabel

/-!
# XOR Line Marked

Apply the XOR-line refinement to marked vertices of an
arbitrary ambient graph. The interface checks only the graph's actual edges.
-/

@[expose] public section

namespace GridHardness.XorLine.Marked

variable {V : Type*} {n : Nat}

structure Isolation (D : V → V → Prop) (embed : Source.Vertex n → V) : Prop where
  internal : ∀ u v, D (embed u) (embed v) ↔ Source.Adj n u v
  outgoing : ∀ u, ¬Source.IsOutput n u → ∀ v, D (embed u) v → ∃ w, v=embed w
  incoming : ∀ v, ¬Source.IsInput n v → ∀ u, D u (embed v) → ∃ w, u=embed w

abbrev Outside (embed : Source.Vertex n → V) := {v : V // v ∉ Set.range embed}
abbrev OriginalVertex (embed : Source.Vertex n → V) := Outside embed ⊕ Source.Vertex n
abbrev ReplacementVertex (embed : Source.Vertex n → V) := Outside embed ⊕ Vertex n

def original (embed : Source.Vertex n → V) : OriginalVertex embed → V
  | .inl o => o.val
  | .inr p => embed p

theorem original_bijective (embed : Source.Vertex n → V) (he : Function.Injective embed) :
    Function.Bijective (original embed) := by
  classical
  constructor
  · rintro (o | p) (o' | p') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact False.elim (o.property ⟨p',h.symm⟩)
    · exact False.elim (o'.property ⟨p,h⟩)
    · exact congrArg Sum.inr (he h)
  · intro v
    by_cases h : v ∈ Set.range embed
    · obtain ⟨p,hp⟩ := h
      exact ⟨.inr p,hp⟩
    · exact ⟨.inl ⟨v,h⟩,rfl⟩

noncomputable def equivToOriginal (embed : Source.Vertex n → V)
    (he : Function.Injective embed) : OriginalVertex embed ≃ V :=
  Equiv.ofBijective (original embed) (original_bijective embed he)

def outside (D : V → V → Prop) (embed : Source.Vertex n → V)
    (u v : Outside embed) : Prop := D u.val v.val
def enter (D : V → V → Prop) (embed : Source.Vertex n → V)
    (u : Outside embed) (p : Port n) : Prop := D u.val (embed (Source.inputPort n p))
def leave (D : V → V → Prop) (embed : Source.Vertex n → V)
    (p : Port n) (u : Outside embed) : Prop := D (embed (Source.outputPort n p)) u.val

theorem source_input_exists (v : Source.Vertex n) (h : Source.IsInput n v) :
    ∃ p : Port n, v=Source.inputPort n p := by
  rcases v with j | ⟨i,b⟩
  · rcases h with rfl | rfl
    · exact ⟨.inl true,rfl⟩
    · exact ⟨.inl false,rfl⟩
  · change b=false at h
    subst b
    exact ⟨.inr i,rfl⟩

theorem source_output_exists (v : Source.Vertex n) (h : Source.IsOutput n v) :
    ∃ p : Port n, v=Source.outputPort n p := by
  rcases v with j | ⟨i,b⟩
  · rcases h with rfl | rfl
    · exact ⟨.inl true,rfl⟩
    · exact ⟨.inl false,rfl⟩
  · change b=true at h
    subst b
    exact ⟨.inr i,rfl⟩

theorem incoming_port (D : V → V → Prop) (embed : Source.Vertex n → V)
    (h : Isolation D embed) (o : Outside embed) (v : Source.Vertex n)
    (ha : D o.val (embed v)) : ∃ p, v=Source.inputPort n p := by
  apply source_input_exists
  by_contra hv
  obtain ⟨u,hu⟩ := h.incoming v hv o.val ha
  exact o.property ⟨u,hu.symm⟩

theorem outgoing_port (D : V → V → Prop) (embed : Source.Vertex n → V)
    (h : Isolation D embed) (o : Outside embed) (v : Source.Vertex n)
    (ha : D (embed v) o.val) : ∃ p, v=Source.outputPort n p := by
  apply source_output_exists
  by_contra hv
  obtain ⟨u,hu⟩ := h.outgoing v hv o.val ha
  exact o.property ⟨u,hu.symm⟩

theorem original_adj_iff (D : V → V → Prop) (embed : Source.Vertex n → V)
    (h : Isolation D embed) (a b : OriginalVertex embed) :
    D (original embed a) (original embed b) ↔
      Source.attached n (outside D embed) (enter D embed) (leave D embed) a b := by
  cases a with
  | inl o =>
    cases b with
    | inl o' => rfl
    | inr v =>
      constructor
      · intro ha
        obtain ⟨p,hv⟩ := incoming_port D embed h o v ha
        refine ⟨p,?_,hv⟩
        simpa only [hv,original,enter] using ha
      · rintro ⟨p,ha,hv⟩
        change D o.val (embed v)
        rw [hv]
        exact ha
  | inr u =>
    cases b with
    | inl o =>
      constructor
      · intro ha
        obtain ⟨p,hu⟩ := outgoing_port D embed h o u ha
        refine ⟨p,?_,hu⟩
        simpa only [hu,original,leave] using ha
      · rintro ⟨p,ha,hu⟩
        change D (embed u) o.val
        rw [hu]
        exact ha
    | inr v => exact h.internal u v

def replacement (D : V → V → Prop) (embed : Source.Vertex n → V) :
    ReplacementVertex embed → ReplacementVertex embed → Prop :=
  attached n (outside D embed) (enter D embed) (leave D embed)

/-- A marked original XOR and marked compulsory arcs can be refined inside
the actual ambient graph. All boundary edges are recovered from that graph. -/
theorem replacement_correct [Finite V] (D : V → V → Prop)
    (embed : Source.Vertex n → V) (he : Function.Injective embed) (h : Isolation D embed) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (replacement D embed) := by
  have hr := PathCover.hamiltonian_relabel_iff
    (Source.attached n (outside D embed) (enter D embed) (leave D embed))
    D (equivToOriginal embed he) (fun u v => (original_adj_iff D embed h u v).symm)
  exact hr.symm.trans (refinement_iff n (outside D embed) (enter D embed) (leave D embed))

theorem replacement_vertex_count [Fintype V] (embed : Source.Vertex n → V)
    (he : Function.Injective embed) :
    Nat.card (ReplacementVertex embed)=Fintype.card V+8*n := by
  classical
  letI : Fintype (Outside embed) := Fintype.ofFinite _
  have ho := Fintype.card_congr (equivToOriginal embed he)
  change Fintype.card (Outside embed ⊕ Source.Vertex n)=Fintype.card V at ho
  rw [Fintype.card_sum,source_vertex_count] at ho
  change Nat.card (Outside embed ⊕ Vertex n)=_
  rw [Nat.card_eq_fintype_card,Fintype.card_sum,target_vertex_count]
  omega

/-- The four compulsory transverse arcs of an XOR, in geometric row order. -/
def crossArc : Fin 4 → Fin 10 := ![5,1,8,4]

theorem crossArc_certificate : ∀ i : Fin 4,
    (XorGadget.arc (crossArc i)).1 ≠ 0 ∧ (XorGadget.arc (crossArc i)).1 ≠ 7 ∧
    ∀ e : Fin 10, (XorGadget.arc e).1=(XorGadget.arc (crossArc i)).1 → e=crossArc i := by
  decide

theorem source_crossArc_unique (i : Fin 4) (v : Source.Vertex n) :
    Source.Adj n (.inl (XorGadget.arc (crossArc i)).1) v ↔
      v=.inl (XorGadget.arc (crossArc i)).2 := by
  cases v with
  | inl j =>
    constructor
    · rintro ⟨e,he⟩
      have hparts := Prod.mk.inj he
      have he' := (crossArc_certificate i).2.2 e hparts.1
      subst e
      exact congrArg Sum.inl hparts.2.symm
    · intro hj
      have hj' := Sum.inl_injective hj
      subst j
      exact ⟨crossArc i,rfl⟩
  | inr p =>
    rcases p with ⟨r,b⟩
    cases b <;> simp [Source.Adj]

/-- These actual ambient arcs satisfy the unique-outgoing condition used by
`MandatoryArcSubdivision.hamiltonian_iff_unique_outgoing`. Their compulsory
traversal does not need to be assumed separately. -/
theorem crossArc_has_unique_outgoing (D : V → V → Prop)
    (embed : Source.Vertex n → V) (h : Isolation D embed) (i : Fin 4) :
    D (embed (.inl (XorGadget.arc (crossArc i)).1))
      (embed (.inl (XorGadget.arc (crossArc i)).2)) ∧
    ∀ v, D (embed (.inl (XorGadget.arc (crossArc i)).1)) v →
      v=embed (.inl (XorGadget.arc (crossArc i)).2) := by
  constructor
  · exact (h.internal _ _).mpr ⟨crossArc i,rfl⟩
  · intro v hv
    have hn : ¬Source.IsOutput n (.inl (XorGadget.arc (crossArc i)).1) :=
      not_or_intro (crossArc_certificate i).1 (crossArc_certificate i).2.1
    obtain ⟨w,rfl⟩ := h.outgoing _ hn v hv
    exact congrArg embed ((source_crossArc_unique i w).mp ((h.internal _ _).mp hv))

end GridHardness.XorLine.Marked
