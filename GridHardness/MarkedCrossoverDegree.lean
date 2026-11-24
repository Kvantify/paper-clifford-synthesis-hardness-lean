/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.MarkedCrossoverReplacement
public import GridHardness.CrossoverDegrees
public import GridHardness.XorWirePortDegree

/-!
# Marked Crossover Degree

Transport in-degree and out-degree bounds through a marked crossover replacement.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.MarkedCrossover.Degree
open XorWire.NetworkDegree (inDegree outDegree)

variable {O C W V : Type*}

noncomputable instance outsideFintype [Fintype V] (embed : C × TwoXorGadget.Vertex → V) :
    Fintype (Outside embed) := Fintype.ofFinite _

abbrev Endpoint (O C : Type*) := O ⊕ (C × (Bool × Bool))

def portMap (port : Bool → Bool → W) : Endpoint O C → O ⊕ (C × W)
  | .inl o => .inl o
  | .inr (c,p) => .inr (c,port p.1 p.2)

theorem portMap_injective (port : Bool → Bool → W)
    (hp : Function.Injective (fun p : Bool × Bool => port p.1 p.2)) :
    Function.Injective (portMap (O := O) (C := C) port) := by
  rintro (o | ⟨c,p⟩) (o' | ⟨c',p'⟩) he
  · exact congrArg Sum.inl (Sum.inl_injective he)
  · cases he
  · cases he
  · obtain ⟨hc,hv⟩ := Prod.mk.inj (Sum.inr_injective he)
    exact congrArg Sum.inr (Prod.ext hc (hp hv))

theorem inDegree_relabel {A B : Type*} [Fintype A] [Fintype B]
    (D : A → A → Prop) (E : B → B → Prop) (e : A ≃ B)
    (he : ∀ a b, D a b ↔ E (e a) (e b)) (v : A) : inDegree D v = inDegree E (e v) := by
  classical
  unfold inDegree
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(he a v).mp (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact e.injective hab
  · intro b hb
    refine ⟨e.symm b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
    apply (he (e.symm b) v).mpr
    simpa using (Finset.mem_filter.mp hb).2

theorem outDegree_relabel {A B : Type*} [Fintype A] [Fintype B]
    (D : A → A → Prop) (E : B → B → Prop) (e : A ≃ B)
    (he : ∀ a b, D a b ↔ E (e a) (e b)) (v : A) : outDegree D v = outDegree E (e v) :=
  inDegree_relabel (fun a b => D b a) (fun a b => E b a) e (fun a b => he b a) v

private theorem unique_external {A B : Type*} [Fintype A]
    (P : A → Prop) (Q : B → Prop) (f : B → A) (hf : Function.Injective f)
    (z : A) (hz : P z) (hn : ∀ b, Q b → f b ≠ z) (he : ∀ b, Q b → P (f b))
    (hb : by classical exact (Finset.univ.filter P).card ≤ 2) :
    ∀ a b, Q a → Q b → a = b := by
  classical
  intro a b ha hc
  by_contra hab
  have hfab : f a ≠ f b := fun h => hab (hf h)
  have hza : z ≠ f a := (hn a ha).symm
  have hzb : z ≠ f b := (hn b hc).symm
  have hs : ({z,f a,f b} : Finset A) ⊆ Finset.univ.filter P := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he a ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he b hc⟩
  have hk := Finset.card_le_card hs
  have hh : ({z,f a,f b} : Finset A).card = 3 := by simp [hza,hzb,hfab]
  omega

section Marked
variable (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)

abbrev Ends := Endpoint (Outside embed) C

def incoming (c : C) (p : Bool × Bool) : Ends embed → Prop
  | .inl o => enter D embed o c p.1 p.2
  | .inr (d,q) => d ≠ c ∧ link D embed d q.1 q.2 c p.1 p.2

def outgoing (c : C) (p : Bool × Bool) : Ends embed → Prop
  | .inl o => leave D embed c p.1 p.2 o
  | .inr (d,q) => c ≠ d ∧ link D embed c p.1 p.2 d q.1 q.2

def sourceIn (u : Ends embed) : V := original embed (portMap TwoXorGadget.output u)
def sourceOut (u : Ends embed) : V := original embed (portMap TwoXorGadget.input u)

theorem sourceIn_injective (he : Function.Injective embed) : Function.Injective (sourceIn embed) :=
  (original_bijective embed he).1.comp (portMap_injective _ TwoXorGadget.output_injective)

theorem sourceOut_injective (he : Function.Injective embed) : Function.Injective (sourceOut embed) :=
  (original_bijective embed he).1.comp (portMap_injective _ TwoXorGadget.input_injective)

private def beforeInput (p : Bool × Bool) : TwoXorGadget.Vertex := (p.1,if p.2 then 2 else 5)
private def afterOutput (p : Bool × Bool) : TwoXorGadget.Vertex := (p.1,if p.2 then 1 else 6)
private theorem input_edge : ∀ p : Bool × Bool,
    TwoXorGadget.Adj (beforeInput p) (TwoXorGadget.input p.1 p.2) := by decide
private theorem output_edge : ∀ p : Bool × Bool,
    TwoXorGadget.Adj (TwoXorGadget.output p.1 p.2) (afterOutput p) := by decide

theorem incoming_unique (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V]
    (hin : ∀ v, inDegree D v ≤ 2) (c : C) (p : Bool × Bool) :
    ∀ a b, incoming D embed c p a → incoming D embed c p b → a = b := by
  classical
  apply unique_external (fun v => D v (embed (c,TwoXorGadget.input p.1 p.2)))
    (incoming D embed c p) (sourceIn embed) (sourceIn_injective embed he)
    (embed (c,beforeInput p)) ((h.same_cell c _ _).mpr (input_edge p))
  · intro u hu hh
    cases u with
    | inl o => exact o.property ⟨(c,beforeInput p),hh.symm⟩
    | inr q =>
      rcases q with ⟨d,q⟩
      exact hu.1 (congrArg Prod.fst (he hh))
  · intro u hu
    cases u with
    | inl o => exact hu
    | inr q => exact hu.2
  · exact hin _

theorem outgoing_unique (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V]
    (hout : ∀ v, outDegree D v ≤ 2) (c : C) (p : Bool × Bool) :
    ∀ a b, outgoing D embed c p a → outgoing D embed c p b → a = b := by
  classical
  apply unique_external (fun v => D (embed (c,TwoXorGadget.output p.1 p.2)) v)
    (outgoing D embed c p) (sourceOut embed) (sourceOut_injective embed he)
    (embed (c,afterOutput p)) ((h.same_cell c _ _).mpr (output_edge p))
  · intro u hu hh
    cases u with
    | inl o => exact o.property ⟨(c,afterOutput p),hh.symm⟩
    | inr q =>
      rcases q with ⟨d,q⟩
      exact hu.1 (congrArg Prod.fst (he hh)).symm
  · intro u hu
    cases u with
    | inl o => exact hu
    | inr q => exact hu.2
  · exact hout _

def extraIn (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed) : Prop :=
  ∃ p z, incoming D embed c p z ∧ v = PlanarSatCrossover.input p.1 p.2 ∧
    u = portMap PlanarSatCrossover.output z

def extraOut (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed) : Prop :=
  ∃ p z, outgoing D embed c p z ∧ v = PlanarSatCrossover.output p.1 p.2 ∧
    u = portMap PlanarSatCrossover.input z

theorem extraIn_unique (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V] (hin : ∀ v, inDegree D v ≤ 2)
    (c : C) (v : PlanarSatCrossover.Vertex) (a b : ReplacementVertex embed)
    (ha : extraIn D embed c v a) (hb : extraIn D embed c v b) : a = b := by
  obtain ⟨p,z,hz,hv,rfl⟩ := ha
  obtain ⟨q,w,hw,hv',rfl⟩ := hb
  have hp := PlanarSatCrossover.input_injective (hv.symm.trans hv')
  subst q
  exact congrArg _ (incoming_unique D embed he h hin c p z w hz hw)

theorem extraOut_unique (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V] (hout : ∀ v, outDegree D v ≤ 2)
    (c : C) (v : PlanarSatCrossover.Vertex) (a b : ReplacementVertex embed)
    (ha : extraOut D embed c v a) (hb : extraOut D embed c v b) : a = b := by
  obtain ⟨p,z,hz,hv,rfl⟩ := ha
  obtain ⟨q,w,hw,hv',rfl⟩ := hb
  have hp := PlanarSatCrossover.output_injective (hv.symm.trans hv')
  subst q
  exact congrArg _ (outgoing_unique D embed he h hout c p z w hz hw)

noncomputable def extraInChoice (c : C) (v : PlanarSatCrossover.Vertex) : ReplacementVertex embed := by
  classical
  exact if h : ∃ u, extraIn D embed c v u then h.choose else .inr (c,PlanarSatCrossover.h 0)
noncomputable def extraOutChoice (c : C) (v : PlanarSatCrossover.Vertex) : ReplacementVertex embed := by
  classical
  exact if h : ∃ u, extraOut D embed c v u then h.choose else .inr (c,PlanarSatCrossover.h 0)

theorem extraIn_choice_eq (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V] (hin : ∀ v, inDegree D v ≤ 2)
    (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed) (hu : extraIn D embed c v u) :
    u = extraInChoice D embed c v := by
  classical
  unfold extraInChoice
  rw [dite_eq_left ⟨u,hu⟩]
  exact extraIn_unique D embed he h hin c v _ _ hu (Exists.choose_spec _)

theorem extraOut_choice_eq (he : Function.Injective embed) (h : CellIsolation D embed) [Fintype V] (hout : ∀ v, outDegree D v ≤ 2)
    (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed) (hu : extraOut D embed c v u) :
    u = extraOutChoice D embed c v := by
  classical
  unfold extraOutChoice
  rw [dite_eq_left ⟨u,hu⟩]
  exact extraOut_unique D embed he h hout c v _ _ hu (Exists.choose_spec _)

theorem incoming_cases (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed)
    (hu : replacement D embed u (.inr (c, v))) :
    (∃ w, PlanarSatCrossover.Adj w v ∧ u = .inr (c,w)) ∨ extraIn D embed c v u := by
  cases u with
  | inl o =>
    obtain ⟨b,s,ha,hv⟩ := hu
    exact Or.inr ⟨(b,s),.inl o,ha,hv,rfl⟩
  | inr p =>
    rcases p with ⟨d,w⟩
    rcases hu with ⟨rfl,ha⟩ | ⟨hd,b,s,k,t,ha,hw,hv⟩
    · exact Or.inl ⟨w,ha,rfl⟩
    · exact Or.inr ⟨(k,t),.inr (d,(b,s)),⟨hd,ha⟩,hv,congrArg (fun z => Sum.inr (d,z)) hw⟩

theorem outgoing_cases (c : C) (v : PlanarSatCrossover.Vertex) (u : ReplacementVertex embed)
    (hu : replacement D embed (.inr (c, v)) u) :
    (∃ w, PlanarSatCrossover.Adj v w ∧ u = .inr (c,w)) ∨ extraOut D embed c v u := by
  cases u with
  | inl o =>
    obtain ⟨b,s,ha,hv⟩ := hu
    exact Or.inr ⟨(b,s),.inl o,ha,hv,rfl⟩
  | inr p =>
    rcases p with ⟨d,w⟩
    rcases hu with ⟨rfl,ha⟩ | ⟨hd,b,s,k,t,ha,hv,hw⟩
    · exact Or.inl ⟨w,ha,rfl⟩
    · exact Or.inr ⟨(b,s),.inr (d,(k,t)),⟨hd,ha⟩,hv,congrArg (fun z => Sum.inr (d,z)) hw⟩

end Marked

private theorem neighbor_card_bound {A B : Type*} [Fintype A] [Fintype B]
    (R : A → Prop) (S : B → Prop) (f : B → A) (P : Prop) (extra : A)
    [DecidablePred R] [DecidablePred S] [Decidable P]
    (h : ∀ a, R a → (∃ b, S b ∧ a = f b) ∨ (P ∧ a = extra)) :
    (Finset.univ.filter R).card ≤ (Finset.univ.filter S).card + if P then 1 else 0 := by
  classical
  have hs : Finset.univ.filter R ⊆ (Finset.univ.filter S).image f ∪ if P then {extra} else ∅ := by
    intro a ha
    rcases h a (Finset.mem_filter.mp ha).2 with ⟨b,hb,rfl⟩ | ⟨hp,rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩)
    · apply Finset.mem_union_right
      simp [hp]
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hi := Finset.card_image_le (s := Finset.univ.filter S) (f := f)
  have hp : (if P then ({extra} : Finset A) else ∅).card = if P then 1 else 0 := by
    split_ifs <;> simp
  omega

private theorem augmented_degrees (v : PlanarSatCrossover.Vertex) :
    PlanarSatCrossover.inDegree v + (if v ∈ PlanarSatCrossover.entries then 1 else 0) ≤ 2 ∧
    PlanarSatCrossover.outDegree v + (if v ∈ PlanarSatCrossover.exits then 1 else 0) ≤ 2 ∧
    (PlanarSatCrossover.inDegree v + (if v ∈ PlanarSatCrossover.entries then 1 else 0)) +
      (PlanarSatCrossover.outDegree v + (if v ∈ PlanarSatCrossover.exits then 1 else 0)) ≤ 3 := by
  have hd := PlanarSatCrossover.degree_bounds v
  have hdis : ∀ v : PlanarSatCrossover.Vertex,
      ¬ (v ∈ PlanarSatCrossover.entries ∧ v ∈ PlanarSatCrossover.exits) := by decide
  by_cases hi : v ∈ PlanarSatCrossover.entries <;> by_cases ho : v ∈ PlanarSatCrossover.exits
  · exact False.elim (hdis v ⟨hi,ho⟩)
  · have hp := PlanarSatCrossover.port_degrees v (Or.inl hi)
    simp only [hi,ho,ite_true,ite_false]
    omega
  · have hp := PlanarSatCrossover.port_degrees v (Or.inr ho)
    simp only [hi,ho,ite_true,ite_false]
    omega
  · simpa only [hi,ho,ite_false,Nat.add_zero] using hd

/-- Every inserted crossover vertex obeys the directed degree bounds,
using only the source graph's in/out bounds and marked-cell isolation. -/
theorem cell_degree_bounds [Fintype V] [Fintype C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed)
    (hin : ∀ v, inDegree D v ≤ 2) (hout : ∀ v, outDegree D v ≤ 2)
    (c : C) (v : PlanarSatCrossover.Vertex) :
    inDegree (replacement D embed) (.inr (c,v)) ≤ 2 ∧
    outDegree (replacement D embed) (.inr (c,v)) ≤ 2 ∧
    inDegree (replacement D embed) (.inr (c,v)) + outDegree (replacement D embed) (.inr (c,v)) ≤ 3 := by
  classical
  have hi : inDegree (replacement D embed) (.inr (c,v)) ≤
      PlanarSatCrossover.inDegree v + if v ∈ PlanarSatCrossover.entries then 1 else 0 := by
    unfold inDegree PlanarSatCrossover.inDegree
    apply neighbor_card_bound _ (fun w => PlanarSatCrossover.Adj w v)
      (fun w => Sum.inr (c,w)) _ (extraInChoice D embed c v)
    intro u hu
    rcases incoming_cases D embed c v u hu with hh | hh
    · exact Or.inl hh
    · refine Or.inr ⟨?_,extraIn_choice_eq D embed he h hin c v u hh⟩
      obtain ⟨p,z,_,rfl,_⟩ := hh
      exact PlanarSatCrossover.input_mem_entries _ _
  have ho : outDegree (replacement D embed) (.inr (c,v)) ≤
      PlanarSatCrossover.outDegree v + if v ∈ PlanarSatCrossover.exits then 1 else 0 := by
    unfold outDegree PlanarSatCrossover.outDegree
    apply neighbor_card_bound _ (fun w => PlanarSatCrossover.Adj v w)
      (fun w => Sum.inr (c,w)) _ (extraOutChoice D embed c v)
    intro u hu
    rcases outgoing_cases D embed c v u hu with hh | hh
    · exact Or.inl hh
    · refine Or.inr ⟨?_,extraOut_choice_eq D embed he h hout c v u hh⟩
      obtain ⟨p,z,_,rfl,_⟩ := hh
      exact PlanarSatCrossover.output_mem_exits _ _
  have hb := augmented_degrees v
  omega

private def outsidePredicates (outside : O → O → Prop)
    (leave : C → Bool → Bool → O → Prop) (o : O) : Endpoint O C → Prop
  | .inl u => outside u o
  | .inr (c,p) => leave c p.1 p.2 o

private def outsideSuccessors (outside : O → O → Prop)
    (enter : O → C → Bool → Bool → Prop) (o : O) : Endpoint O C → Prop
  | .inl u => outside o u
  | .inr (c,p) => enter o c p.1 p.2

private theorem network_outside_inDegree [Fintype O] [Fintype C] [Fintype W]
    (outside : O → O → Prop) (inside : W → W → Prop) (input output : Bool → Bool → W)
    (enter : O → C → Bool → Bool → Prop) (leave : C → Bool → Bool → O → Prop)
    (link : C → Bool → Bool → C → Bool → Bool → Prop)
    (hinj : Function.Injective (fun p : Bool × Bool => output p.1 p.2)) (o : O) :
    by classical exact inDegree (GadgetNetwork.Adj outside inside input output enter leave link) (.inl o) =
      (Finset.univ.filter (outsidePredicates outside leave o)).card := by
  classical
  have he : Finset.univ.filter
      (fun u => GadgetNetwork.Adj outside inside input output enter leave link u (.inl o)) =
      (Finset.univ.filter (outsidePredicates outside leave o)).image (portMap output) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      cases u with
      | inl u => exact ⟨.inl u,h,rfl⟩
      | inr q =>
        rcases q with ⟨c,w⟩
        obtain ⟨b,t,hl,hv⟩ := h
        exact ⟨.inr (c,(b,t)),hl,congrArg (fun z => Sum.inr (c,z)) hv.symm⟩
    · rintro ⟨u,hu,rfl⟩
      cases u with
      | inl u => exact hu
      | inr q => rcases q with ⟨c,b,t⟩; exact ⟨b,t,hu,rfl⟩
  unfold inDegree
  rw [he,Finset.card_image_of_injective _ (portMap_injective output hinj)]

private theorem network_outside_outDegree [Fintype O] [Fintype C] [Fintype W]
    (outside : O → O → Prop) (inside : W → W → Prop) (input output : Bool → Bool → W)
    (enter : O → C → Bool → Bool → Prop) (leave : C → Bool → Bool → O → Prop)
    (link : C → Bool → Bool → C → Bool → Bool → Prop)
    (hinj : Function.Injective (fun p : Bool × Bool => input p.1 p.2)) (o : O) :
    by classical exact outDegree (GadgetNetwork.Adj outside inside input output enter leave link) (.inl o) =
      (Finset.univ.filter (outsideSuccessors outside enter o)).card := by
  classical
  have he : Finset.univ.filter
      (fun u => GadgetNetwork.Adj outside inside input output enter leave link (.inl o) u) =
      (Finset.univ.filter (outsideSuccessors outside enter o)).image (portMap input) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      cases u with
      | inl u => exact ⟨.inl u,h,rfl⟩
      | inr q =>
        rcases q with ⟨c,w⟩
        obtain ⟨b,t,hl,hv⟩ := h
        exact ⟨.inr (c,(b,t)),hl,congrArg (fun z => Sum.inr (c,z)) hv.symm⟩
    · rintro ⟨u,hu,rfl⟩
      cases u with
      | inl u => exact hu
      | inr q => rcases q with ⟨c,b,t⟩; exact ⟨b,t,hu,rfl⟩
  unfold outDegree
  rw [he,Finset.card_image_of_injective _ (portMap_injective input hinj)]

/-- Outside vertices keep exactly the same incoming degree. -/
theorem outside_inDegree_eq [Fintype V] [Fintype C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed) (o : Outside embed) :
    inDegree (replacement D embed) (.inl o) = inDegree D o.val := by
  classical
  have hr := inDegree_relabel
    (TwoXorGadget.network (outside D embed) (enter D embed) (leave D embed) (link D embed)) D
    (equivToOriginal embed he) (fun a b => (original_adj_iff D embed he h a b).symm) (.inl o)
  have hs := network_outside_inDegree (outside D embed) TwoXorGadget.Adj
    TwoXorGadget.input TwoXorGadget.output (enter D embed) (leave D embed) (link D embed)
    TwoXorGadget.output_injective o
  have ht := network_outside_inDegree (outside D embed) PlanarSatCrossover.Adj
    PlanarSatCrossover.input PlanarSatCrossover.output (enter D embed) (leave D embed) (link D embed)
    PlanarSatCrossover.output_injective o
  exact ht.trans (hs.symm.trans hr)

/-- Outside vertices keep exactly the same outgoing degree. -/
theorem outside_outDegree_eq [Fintype V] [Fintype C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed) (o : Outside embed) :
    outDegree (replacement D embed) (.inl o) = outDegree D o.val := by
  classical
  have hr := outDegree_relabel
    (TwoXorGadget.network (outside D embed) (enter D embed) (leave D embed) (link D embed)) D
    (equivToOriginal embed he) (fun a b => (original_adj_iff D embed he h a b).symm) (.inl o)
  have hs := network_outside_outDegree (outside D embed) TwoXorGadget.Adj
    TwoXorGadget.input TwoXorGadget.output (enter D embed) (leave D embed) (link D embed)
    TwoXorGadget.input_injective o
  have ht := network_outside_outDegree (outside D embed) PlanarSatCrossover.Adj
    PlanarSatCrossover.input PlanarSatCrossover.output (enter D embed) (leave D embed) (link D embed)
    PlanarSatCrossover.input_injective o
  exact ht.trans (hs.symm.trans hr)

/-- Replacing all marked XOR pairs preserves the directed in/out bounds
needed by the certified four-path reduction to subcubic bipartite graphs. -/
theorem replacement_in_out_bounds [Fintype V] [Fintype C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed)
    (hin : ∀ v, inDegree D v ≤ 2) (hout : ∀ v, outDegree D v ≤ 2)
    (v : ReplacementVertex embed) :
    inDegree (replacement D embed) v ≤ 2 ∧ outDegree (replacement D embed) v ≤ 2 := by
  cases v with
  | inl o =>
    rw [outside_inDegree_eq D embed he h,outside_outDegree_eq D embed he h]
    exact ⟨hin _,hout _⟩
  | inr p =>
    rcases p with ⟨c,v⟩
    have h := cell_degree_bounds D embed he h hin hout c v
    exact ⟨h.1,h.2.1⟩

/-- Total directed degree at most three is also preserved, when present
in the ambient graph. No planarity hypothesis enters this graph theorem. -/
theorem replacement_degree_bounds [Fintype V] [Fintype C]
    (D : V → V → Prop) (embed : C × TwoXorGadget.Vertex → V)
    (he : Function.Injective embed) (h : CellIsolation D embed)
    (hin : ∀ v, inDegree D v ≤ 2) (hout : ∀ v, outDegree D v ≤ 2)
    (htotal : ∀ v, inDegree D v + outDegree D v ≤ 3) (v : ReplacementVertex embed) :
    inDegree (replacement D embed) v ≤ 2 ∧ outDegree (replacement D embed) v ≤ 2 ∧
    inDegree (replacement D embed) v + outDegree (replacement D embed) v ≤ 3 := by
  cases v with
  | inl o =>
    rw [outside_inDegree_eq D embed he h,outside_outDegree_eq D embed he h]
    exact ⟨hin _,hout _,htotal _⟩
  | inr p =>
    rcases p with ⟨c,v⟩
    exact cell_degree_bounds D embed he h hin hout c v

end GridHardness.MarkedCrossover.Degree
