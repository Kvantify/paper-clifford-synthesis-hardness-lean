/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CrossoverNetwork
public import GridHardness.HamiltonianRelabel

/-!
# Marked Crossover Replacement

Replace disjoint marked pairs of XORs in an actual ambient directed
graph. The outside vertices are its explicit complement. Exact adjacency
and ordinary nonport isolation derive the boundary network; no Hamiltonian
route or truth-assignment promise is part of the interface.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.MarkedCrossover
variable {V C : Type*}

/-- Graph-level isolation of each marked pair of XOR gadgets. -/
structure CellIsolation (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V) : Prop where
  same_cell : ∀ c u v, D (embed (c,u)) (embed (c,v)) ↔ TwoXorGadget.Adj u v
  outgoing : ∀ c u, u ∉ TwoXorGadget.exits → ∀ v, D (embed (c,u)) v →
    ∃ w, v = embed (c,w)
  incoming : ∀ c v, v ∉ TwoXorGadget.entries → ∀ u, D u (embed (c,v)) →
    ∃ w, u = embed (c,w)

abbrev Outside (embed : C × TwoXorGadget.Vertex → V) := {v : V // v ∉ Set.range embed}
abbrev SourceVertex (embed : C × TwoXorGadget.Vertex → V) := Outside embed ⊕ (C × TwoXorGadget.Vertex)
abbrev ReplacementVertex (embed : C × TwoXorGadget.Vertex → V) :=
  Outside embed ⊕ (C × PlanarSatCrossover.Vertex)

def original (embed : C × TwoXorGadget.Vertex → V) : SourceVertex embed → V
  | .inl o => o.val
  | .inr p => embed p

theorem original_bijective (embed : C × TwoXorGadget.Vertex → V) (he : Function.Injective embed) :
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

noncomputable def equivToOriginal (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) : SourceVertex embed ≃ V :=
  Equiv.ofBijective (original embed) (original_bijective embed he)

@[simp] theorem equivToOriginal_apply (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (v : SourceVertex embed) :
    equivToOriginal embed he v = original embed v := rfl

def outside (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (u v : Outside embed) : Prop := D u.val v.val

def enter (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (u : Outside embed) (c : C) (b s : Bool) : Prop :=
  D u.val (embed (c,TwoXorGadget.input b s))

def leave (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (c : C) (b s : Bool) (u : Outside embed) : Prop :=
  D (embed (c,TwoXorGadget.output b s)) u.val

def link (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (c : C) (b s : Bool) (d : C) (k t : Bool) : Prop :=
  D (embed (c,TwoXorGadget.output b s)) (embed (d,TwoXorGadget.input k t))

private theorem mem_exits_iff : ∀ u : TwoXorGadget.Vertex,
    u ∈ TwoXorGadget.exits ↔ ∃ b s, u = TwoXorGadget.output b s := by decide

private theorem mem_entries_iff : ∀ u : TwoXorGadget.Vertex,
    u ∈ TwoXorGadget.entries ↔ ∃ b s, u = TwoXorGadget.input b s := by decide

theorem outgoing_port (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (h : CellIsolation D embed) (c : C) (u : TwoXorGadget.Vertex) (v : V)
    (ha : D (embed (c, u)) v) (hn : ¬∃ w, v = embed (c,w)) :
    ∃ b s, u = TwoXorGadget.output b s := by
  apply (mem_exits_iff u).mp
  by_contra hu
  exact hn (h.outgoing c u hu v ha)

theorem incoming_port (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (h : CellIsolation D embed) (c : C) (v : TwoXorGadget.Vertex) (u : V)
    (ha : D u (embed (c, v))) (hn : ¬∃ w, u = embed (c,w)) :
    ∃ b s, v = TwoXorGadget.input b s := by
  apply (mem_entries_iff v).mp
  by_contra hv
  exact hn (h.incoming c v hv u ha)

/-- The ambient graph is exactly the network derived from its own edges. -/
theorem original_adj_iff (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed) (a b : SourceVertex embed) :
    D (original embed a) (original embed b) ↔
      TwoXorGadget.network (outside D embed) (enter D embed) (leave D embed) (link D embed) a b := by
  classical
  cases a with
  | inl o =>
    cases b with
    | inl o' => rfl
    | inr p =>
      rcases p with ⟨c,v⟩
      constructor
      · intro ha
        obtain ⟨k,t,hv⟩ := incoming_port D embed h c v o.val ha (by
          rintro ⟨w,hw⟩
          exact o.property ⟨(c,w),hw.symm⟩)
        refine ⟨k,t,?_,hv⟩
        simpa only [hv,original,enter] using ha
      · rintro ⟨k,t,ha,hv⟩
        change D o.val (embed (c,v))
        rw [hv]
        exact ha
  | inr p =>
    rcases p with ⟨c,u⟩
    cases b with
    | inl o =>
      constructor
      · intro ha
        obtain ⟨k,t,hu⟩ := outgoing_port D embed h c u o.val ha (by
          rintro ⟨w,hw⟩
          exact o.property ⟨(c,w),hw.symm⟩)
        refine ⟨k,t,?_,hu⟩
        simpa only [hu,original,leave] using ha
      · rintro ⟨k,t,ha,hu⟩
        change D (embed (c,u)) o.val
        rw [hu]
        exact ha
    | inr p =>
      rcases p with ⟨d,v⟩
      by_cases hcd : c=d
      · subst d
        constructor
        · intro ha
          exact Or.inl ⟨rfl,(h.same_cell c u v).mp ha⟩
        · intro ha
          exact (h.same_cell c u v).mpr ((ha.resolve_right (fun h => h.1 rfl)).2)
      · constructor
        · intro ha
          obtain ⟨k,t,hu⟩ := outgoing_port D embed h c u (embed (d,v)) ha (by
            rintro ⟨w,hw⟩
            exact hcd (congrArg Prod.fst (he hw)).symm)
          obtain ⟨b,s,hv⟩ := incoming_port D embed h d v (embed (c,u)) ha (by
            rintro ⟨w,hw⟩
            exact hcd (congrArg Prod.fst (he hw)))
          refine Or.inr ⟨hcd,k,t,b,s,?_,hu,hv⟩
          simpa only [hu,hv,original,link] using ha
        · rintro (⟨hc,_⟩ | ⟨_,k,t,b,s,ha,hu,hv⟩)
          · exact False.elim (hcd hc)
          · change D (embed (c,u)) (embed (d,v))
            rw [hu,hv]
            exact ha

/-- The replacement graph retains the actual outside edges and exact named
boundary links, replacing only each marked 16-vertex cell by 56 vertices. -/
def replacement (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V) :
    ReplacementVertex embed → ReplacementVertex embed → Prop :=
  PlanarSatCrossover.network (outside D embed) (enter D embed) (leave D embed) (link D embed)

/-- Full graph-level replacement of disjoint marked pairs in an actual
ambient graph. Geometry and the choice of marked pairs remain separate. -/
theorem replacement_correct [Finite V] [Finite C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (replacement D embed) := by
  have hr := PathCover.hamiltonian_relabel_iff
    (TwoXorGadget.network (outside D embed) (enter D embed) (leave D embed) (link D embed))
    D (equivToOriginal embed he) (fun u v => (original_adj_iff D embed he h u v).symm)
  exact hr.symm.trans (crossover_network_correct (outside D embed) (enter D embed)
    (leave D embed) (link D embed))

/-- Each marked pair contributes precisely forty new vertices. -/
theorem replacement_vertex_count [Fintype V] [Fintype C]
    (embed : C × TwoXorGadget.Vertex → V) (he : Function.Injective embed) :
    Nat.card (ReplacementVertex embed) = Fintype.card V + 40 * Fintype.card C := by
  classical
  letI : Fintype (Outside embed) := Fintype.ofFinite _
  have hc := crossover_network_vertex_count (O := Outside embed) (C := C)
  have ho := Fintype.card_congr (equivToOriginal embed he)
  change Fintype.card (Outside embed ⊕ (C × TwoXorGadget.Vertex)) = Fintype.card V at ho
  simpa only [Nat.card_eq_fintype_card,ho] using hc

end GridHardness.MarkedCrossover
