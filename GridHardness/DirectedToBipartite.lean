/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrbitHamiltonian
public import GridHardness.OrbitBlocks
public import GridHardness.Hamiltonian
public import Mathlib.Tactic.FinCases
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Directed To Bipartite

Split every directed vertex into a path in a bipartite graph. Hamiltonian cycles
correspond to single-orbit successor maps of the directed graph.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.DirectedToBipartite

variable {V : Type*}

/-- Replace each directed vertex by an undirected path of four vertices. -/
def graph (D : V → V → Prop) : SimpleGraph (V × Fin 4) where
  Adj x y :=
    (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.2 = 3 ∧ y.2 = 0 ∧ D x.1 y.1) ∨
    (x.2 = 0 ∧ y.2 = 3 ∧ D y.1 x.1)
  symm := ⟨by
    rintro x y (⟨h, h'⟩ | h | h)
    · exact Or.inl ⟨h.symm, h'.symm⟩
    · exact Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)⟩
  loopless := ⟨by
    rintro x (⟨_, h⟩ | h | h)
    · omega
    · have := h.1.symm.trans h.2.1; contradiction
    · have := h.1.symm.trans h.2.1; contradiction⟩

@[simp] theorem adj_one (D : V → V → Prop) (v : V) (x : V × Fin 4) :
    (graph D).Adj (v, 1) x ↔ x = (v, 0) ∨ x = (v, 2) := by
  rcases x with ⟨w, i⟩
  fin_cases i <;> simp [graph, Prod.ext_iff, eq_comm]

@[simp] theorem adj_two (D : V → V → Prop) (v : V) (x : V × Fin 4) :
    (graph D).Adj (v, 2) x ↔ x = (v, 1) ∨ x = (v, 3) := by
  rcases x with ⟨w, i⟩
  fin_cases i <;> simp [graph, Prod.ext_iff, eq_comm]

/-- The construction is bipartite: parity of the path position is a coloring. -/
theorem adjacent_parity_ne (D : V → V → Prop) {x y : V × Fin 4}
    (h : (graph D).Adj x y) : x.2.val % 2 ≠ y.2.val % 2 := by
  rcases x with ⟨v,i⟩; rcases y with ⟨w,j⟩
  fin_cases i <;> fin_cases j <;> simp_all [graph]

/-- Explicit bipartition, with the two colors given by path-position parity. -/
def coloring (D : V → V → Prop) : (graph D).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun x => ⟨x.2.val % 2,Nat.mod_lt _ (by decide)⟩)
    (fun h he => adjacent_parity_ne D h (congrArg Fin.val he))

theorem colorable_two (D : V → V → Prop) : (graph D).Colorable 2 := ⟨coloring D⟩

/-- Traversal of a replaced vertex follows all three internal path edges. -/
def Forward (next : (V × Fin 4) ≃ (V × Fin 4)) (v : V) : Prop :=
  next (v,0) = (v,1) ∧ next (v,1) = (v,2) ∧ next (v,2) = (v,3)

def Backward (next : (V × Fin 4) ≃ (V × Fin 4)) (v : V) : Prop :=
  next (v,3) = (v,2) ∧ next (v,2) = (v,1) ∧ next (v,1) = (v,0)

private theorem no_two_cycle [Nonempty V] (next : (V × Fin 4) ≃ (V × Fin 4))
    (ho : OneOrbit next) {x y : V × Fin 4} (hxy : next x = y) : next y ≠ x := by
  intro hyx
  have hspan := ho.closed_spans (P := fun z => z = x ∨ z = y) (a := x)
    (Or.inl rfl) (by
      intro z hz
      rcases hz with rfl | rfl
      · exact Or.inr hxy
      · exact Or.inl hyx)
  obtain ⟨v⟩ := ‹Nonempty V›
  have h0 := hspan (v,0)
  have h1 := hspan (v,1)
  have h2 := hspan (v,2)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
      first | have he := congrArg Prod.snd (h0.trans h1.symm); simp at he
            | have he := congrArg Prod.snd (h0.trans h2.symm); simp at he
            | have he := congrArg Prod.snd (h1.trans h2.symm); simp at he

/-- The two internal degree-two vertices force one orientation of the entire path. -/
theorem forward_or_backward [Nonempty V] (D : V → V → Prop)
    (next : (V × Fin 4) ≃ (V × Fin 4)) (ho : OneOrbit next)
    (ha : ∀ x, (graph D).Adj x (next x)) (v : V) : Forward next v ∨ Backward next v := by
  have h1 := (adj_one D v _).mp (ha (v,1))
  have h2 := (adj_two D v _).mp (ha (v,2))
  rcases h1 with h10 | h12
  · have h21 : next (v,2) = (v,1) := by
      rcases h2 with h21 | h23
      · exact h21
      obtain ⟨x,hx⟩ := next.surjective (v,1)
      have hadj : (graph D).Adj (v,1) x := by
        simpa only [hx] using ((ha x).symm)
      rcases (adj_one D v x).mp hadj with rfl | rfl
      · exact False.elim (no_two_cycle next ho hx h10)
      · exact False.elim (by rw [h23] at hx; cases hx)
    have h32 : next (v,3) = (v,2) := by
      obtain ⟨x,hx⟩ := next.surjective (v,2)
      have hadj : (graph D).Adj (v,2) x := by
        simpa only [hx] using ((ha x).symm)
      rcases (adj_two D v x).mp hadj with rfl | rfl
      · rw [h10] at hx; cases hx
      · exact hx
    exact Or.inr ⟨h32,h21,h10⟩
  · have h23 : next (v,2) = (v,3) :=
      h2.resolve_left (no_two_cycle next ho h12)
    have h01 : next (v,0) = (v,1) := by
      obtain ⟨x,hx⟩ := next.surjective (v,1)
      have hadj : (graph D).Adj (v,1) x := by
        simpa only [hx] using ((ha x).symm)
      rcases (adj_one D v x).mp hadj with rfl | rfl
      · exact hx
      · rw [h23] at hx; cases hx
    exact Or.inl ⟨h01,h12,h23⟩

@[simp] theorem adj_three (D : V → V → Prop) (v : V) (x : V × Fin 4) :
    (graph D).Adj (v, 3) x ↔ x = (v, 2) ∨ ∃ w, x = (w,0) ∧ D v w := by
  rcases x with ⟨w, i⟩
  fin_cases i <;> simp [graph, Prod.ext_iff, eq_comm]

theorem forward_exit (D : V → V → Prop)
    (next : (V × Fin 4) ≃ (V × Fin 4))
    (ha : ∀ x, (graph D).Adj x (next x)) {v : V} (hf : Forward next v) :
    ∃ w, next (v,3) = (w,0) ∧ D v w := by
  refine ((adj_three D v _).mp (ha (v,3))).resolve_left ?_
  intro h
  have he := congrArg Prod.snd (next.injective (h.trans hf.2.1.symm))
  simp at he

/-- One global cycle cannot traverse different replaced vertices in opposite directions. -/
theorem all_forward_of_forward [Nonempty V] (D : V → V → Prop)
    (next : (V × Fin 4) ≃ (V × Fin 4)) (ho : OneOrbit next)
    (ha : ∀ x, (graph D).Adj x (next x)) {v : V} (hf : Forward next v) :
    ∀ w, Forward next w := by
  have hc : ∀ x : V × Fin 4, Forward next x.1 → Forward next (next x).1 := by
    rintro ⟨w,i⟩ hw
    change Forward next w at hw
    fin_cases i
    · change Forward next (next (w,0)).1; rw [hw.1]; exact hw
    · change Forward next (next (w,1)).1; rw [hw.2.1]; exact hw
    · change Forward next (next (w,2)).1; rw [hw.2.2]; exact hw
    · change Forward next (next (w,3)).1
      obtain ⟨z,hz,_⟩ := forward_exit D next ha hw
      rw [hz]
      rcases forward_or_backward D next ho ha z with hzf | hzb
      · exact hzf
      · have he := congrArg Prod.snd (next.injective (hz.trans hzb.2.2.symm))
        simp at he
  intro w
  exact ho.closed_spans (P := fun x => Forward next x.1) (a := (v,0)) hf hc (w,0)

/-- Contract the forced internal paths in a consistently oriented spanning orbit. -/
theorem contract_forward (D : V → V → Prop)
    (next : (V × Fin 4) ≃ (V × Fin 4)) (ho : OneOrbit next)
    (ha : ∀ x, (graph D).Adj x (next x)) (hf : ∀ v, Forward next v) :
    ∃ f : V ≃ V, OneOrbit f ∧ ∀ v, D v (f v) := by
  let f : V → V := fun v => (next (v,3)).1
  have he : ∀ v, next (v,3) = (f v,0) := by
    intro v
    obtain ⟨w,hw,_⟩ := forward_exit D next ha (hf v)
    dsimp [f]
    rw [hw]
  have hd : ∀ v, D v (f v) := by
    intro v
    obtain ⟨w,hw,hd⟩ := forward_exit D next ha (hf v)
    simpa only [f,hw] using hd
  have hi : Function.Injective f := by
    intro v w hvw
    have h := next.injective ((he v).trans ((congrArg (fun z : V => (z, (0 : Fin 4))) hvw).trans (he w).symm))
    exact congrArg Prod.fst h
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨⟨v,i⟩,h⟩ := next.surjective (w,0)
    fin_cases i
    · change next (v,0) = (w,0) at h
      rw [(hf v).1] at h; cases h
    · change next (v,1) = (w,0) at h
      rw [(hf v).2.1] at h; cases h
    · change next (v,2) = (w,0) at h
      rw [(hf v).2.2] at h; cases h
    · exact ⟨v,congrArg Prod.fst h⟩
  let e : V ≃ V := Equiv.ofBijective f ⟨hi,hs⟩
  refine ⟨e, ?_, hd⟩
  intro u v
  have hc : ∀ x : V × Fin 4, (∃ n, (f^[n]) u = x.1) →
      ∃ n, (f^[n]) u = (next x).1 := by
    rintro ⟨w,i⟩ ⟨n,hn⟩
    change (f^[n]) u = w at hn
    fin_cases i
    · refine ⟨n, ?_⟩
      change (f^[n]) u = (next (w,0)).1
      rw [(hf w).1]; exact hn
    · refine ⟨n, ?_⟩
      change (f^[n]) u = (next (w,1)).1
      rw [(hf w).2.1]; exact hn
    · refine ⟨n, ?_⟩
      change (f^[n]) u = (next (w,2)).1
      rw [(hf w).2.2]; exact hn
    · refine ⟨n+1, ?_⟩
      change (f^[n+1]) u = (next (w,3)).1
      rw [Function.iterate_succ_apply',hn,he]
  exact ho.closed_spans (P := fun x => ∃ n, (f^[n]) u = x.1)
    (a := (u,0)) ⟨0,rfl⟩ hc (v,0)

/-- Expand a directed successor permutation through the four path positions. -/
def expand (f : V ≃ V) : (V × Fin 4) ≃ (V × Fin 4) where
  toFun x := ![(x.1,1),(x.1,2),(x.1,3),(f x.1,0)] x.2
  invFun x := ![(f.symm x.1,3),(x.1,0),(x.1,1),(x.1,2)] x.2
  left_inv := by rintro ⟨v,i⟩; fin_cases i <;> simp
  right_inv := by rintro ⟨v,i⟩; fin_cases i <;> simp

@[simp] theorem expand_zero (f : V ≃ V) (v : V) : expand f (v,0) = (v,1) := rfl
@[simp] theorem expand_one (f : V ≃ V) (v : V) : expand f (v,1) = (v,2) := rfl
@[simp] theorem expand_two (f : V ≃ V) (v : V) : expand f (v,2) = (v,3) := rfl
@[simp] theorem expand_three (f : V ≃ V) (v : V) : expand f (v,3) = (f v,0) := rfl

/-- The expansion preserves the directed spanning orbit. -/
theorem expand_oneOrbit (f : V ≃ V) (ho : OneOrbit f) : OneOrbit (expand f) :=
  ho.four_blocks (expand f) (expand_zero f) (expand_one f) (expand_two f) (expand_three f)

theorem expand_adjacent (D : V → V → Prop) (f : V ≃ V) (hd : ∀ v, D v (f v)) :
    ∀ x, (graph D).Adj x (expand f x) := by
  rintro ⟨v,i⟩
  fin_cases i <;> simp [expand,graph,hd]

/-- Replacing directed vertices by four-vertex paths exactly preserves Hamiltonicity,
expressed as a successor permutation with a single spanning orbit. -/
theorem oneOrbit_iff [Nonempty V] (D : V → V → Prop) :
    (∃ f : V ≃ V, OneOrbit f ∧ ∀ v, D v (f v)) ↔
      ∃ next : (V × Fin 4) ≃ (V × Fin 4),
        OneOrbit next ∧ ∀ x, (graph D).Adj x (next x) := by
  constructor
  · rintro ⟨f,ho,hd⟩
    exact ⟨expand f,expand_oneOrbit f ho,expand_adjacent D f hd⟩
  · rintro ⟨next,ho,ha⟩
    obtain ⟨v⟩ := ‹Nonempty V›
    rcases forward_or_backward D next ho ha v with hf | hb
    · exact contract_forward D next ho ha (all_forward_of_forward D next ho ha hf)
    · have hos := ho.symm
      have has : ∀ x, (graph D).Adj x (next.symm x) := by
        intro x
        simpa using (ha (next.symm x)).symm
      have hfs : Forward next.symm v := by
        exact ⟨next.symm_apply_eq.mpr hb.2.2.symm,
          next.symm_apply_eq.mpr hb.2.1.symm,next.symm_apply_eq.mpr hb.1.symm⟩
      exact contract_forward D next.symm hos has
        (all_forward_of_forward D next.symm hos has hfs)

/-- Correctness against mathlib's actual Hamiltonian-cycle walks. -/
theorem hamiltonianCycle_iff [Fintype V] [DecidableEq V] [Nonempty V]
    (D : V → V → Prop) :
    (∃ (x : V × Fin 4) (p : (graph D).Walk x x), p.IsHamiltonianCycle) ↔
      ∃ f : V ≃ V, OneOrbit f ∧ ∀ v, D v (f v) := by
  have h3 : 3 ≤ Fintype.card (V × Fin 4) := by
    rw [Fintype.card_prod,Fintype.card_fin]
    have := Fintype.card_pos (α := V)
    omega
  exact (hamiltonianCycle_iff_oneOrbit (graph D) h3).trans (oneOrbit_iff D).symm

/-- Total-instance formulation: a directed Hamiltonian cycle must contain a vertex. -/
theorem hamiltonianCycle_iff_nonempty [Fintype V] [DecidableEq V]
    (D : V → V → Prop) :
    (∃ (x : V × Fin 4) (p : (graph D).Walk x x), p.IsHamiltonianCycle) ↔
      Nonempty V ∧ ∃ f : V ≃ V, OneOrbit f ∧ ∀ v, D v (f v) := by
  constructor
  · intro h
    obtain ⟨x,p,hp⟩ := h
    haveI : Nonempty V := ⟨x.1⟩
    exact ⟨inferInstance,(hamiltonianCycle_iff D).mp ⟨x,p,hp⟩⟩
  · rintro ⟨hn,h⟩
    haveI : Nonempty V := hn
    exact (hamiltonianCycle_iff D).mpr h

/-- Exactly four output vertices are used per directed input vertex. -/
@[simp] theorem card_vertices [Fintype V] :
    Fintype.card (V × Fin 4) = 4 * Fintype.card V := by simp [Nat.mul_comm]

section Degree
variable [Fintype V] [DecidableEq V] (D : V → V → Prop) [DecidableRel D]

instance : DecidableRel (graph D).Adj := fun x y => by
  unfold graph
  infer_instance

private theorem neighbors_zero (v : V) :
    (graph D).neighborFinset (v,0) =
      (Finset.univ.filter (fun w => D w v)).image (fun w => (w,(3 : Fin 4))) ∪ {(v,1)} := by
  ext ⟨w,i⟩
  fin_cases i <;> simp [SimpleGraph.mem_neighborFinset,graph,eq_comm]

private theorem neighbors_three (v : V) :
    (graph D).neighborFinset (v,3) =
      (Finset.univ.filter (fun w => D v w)).image (fun w => (w,(0 : Fin 4))) ∪ {(v,2)} := by
  ext ⟨w,i⟩
  fin_cases i <;> simp [SimpleGraph.mem_neighborFinset,graph,eq_comm]

@[simp] theorem degree_one (v : V) : (graph D).degree (v,1) = 2 := by
  have he : (graph D).neighborFinset (v,1) = {(v,0),(v,2)} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset,adj_one,Finset.mem_insert,
      Finset.mem_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
  simp

@[simp] theorem degree_two (v : V) : (graph D).degree (v,2) = 2 := by
  have he : (graph D).neighborFinset (v,2) = {(v,1),(v,3)} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset,adj_two,Finset.mem_insert,
      Finset.mem_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
  simp

/-- Directed in- and out-degree at most two give undirected degree at most three. -/
theorem degree_le_three
    (hin : ∀ v, (Finset.univ.filter (fun w => D w v)).card ≤ 2)
    (hout : ∀ v, (Finset.univ.filter (fun w => D v w)).card ≤ 2)
    (x : V × Fin 4) : (graph D).degree x ≤ 3 := by
  rcases x with ⟨v,i⟩
  fin_cases i
  · change (graph D).degree (v,0) ≤ 3
    rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_zero]
    have h := Finset.card_union_le
      ((Finset.univ.filter (fun w => D w v)).image (fun w => (w,(3 : Fin 4)))) {(v,1)}
    have hi := Finset.card_image_le (s := Finset.univ.filter (fun w => D w v))
      (f := fun w => (w,(3 : Fin 4)))
    simpa only [Finset.card_singleton] using h.trans (Nat.add_le_add_right (hi.trans (hin v)) 1)
  · change (graph D).degree (v,1) ≤ 3
    simp
  · change (graph D).degree (v,2) ≤ 3
    simp
  · change (graph D).degree (v,3) ≤ 3
    rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors_three]
    have h := Finset.card_union_le
      ((Finset.univ.filter (fun w => D v w)).image (fun w => (w,(0 : Fin 4)))) {(v,2)}
    have hi := Finset.card_image_le (s := Finset.univ.filter (fun w => D v w))
      (f := fun w => (w,(0 : Fin 4)))
    simpa only [Finset.card_singleton] using h.trans (Nat.add_le_add_right (hi.trans (hout v)) 1)

end Degree

end GridHardness.DirectedToBipartite
