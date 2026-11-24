/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedOrbit
public import GridHardness.Hamiltonian

/-!
# Orbit Hamiltonian

A bridge between directed successor witnesses and mathlib's walk-based
Hamiltonian cycles. The cardinality hypothesis excludes traversing a single
undirected edge twice.
-/

public section

namespace GridHardness

open SimpleGraph

theorem oneOrbit_finRotate (n : Nat) : OneOrbit (finRotate n) := by
  intro u v
  have : NeZero n := u.neZero
  refine ⟨(v - u).val, ?_⟩
  rw [← finCycle_eq_finRotate_iterate, finCycle_apply]
  simp [sub_eq_add_neg]

theorem OneOrbit.transport {V W : Type*} {next : V → V} {step : W → W}
    (h : OneOrbit next) (e : V ≃ W) (he : ∀ v, step (e v) = e (next v)) :
    OneOrbit step := by
  have hi : ∀ n v, (step^[n]) (e v) = e ((next^[n]) v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, he, Function.iterate_succ_apply']
  intro u v
  obtain ⟨n, hn⟩ := h (e.symm u) (e.symm v)
  refine ⟨n, ?_⟩
  simpa [hn] using hi n (e.symm u)

/-- Reversing every edge reverses the spanning orbit. -/
theorem OneOrbit.symm {V : Type*} {next : V ≃ V} (h : OneOrbit next) :
    OneOrbit next.symm := by
  intro u v
  obtain ⟨n, hn⟩ := h v u
  refine ⟨n, ?_⟩
  rw [← hn]
  exact Function.LeftInverse.iterate next.symm_apply_apply n v

/-- A spanning orbit supplies a predecessor for each vertex. -/
theorem OneOrbit.surjective {V : Type*} {next : V → V} (h : OneOrbit next) :
    Function.Surjective next := by
  classical
  intro v
  by_cases hall : ∀ u : V, u = v
  · exact ⟨v, hall (next v)⟩
  · obtain ⟨u, hu⟩ := not_forall.mp hall
    obtain ⟨n, hn⟩ := h u v
    cases n with
    | zero => exact False.elim (hu hn)
    | succ n =>
      exact ⟨(next^[n]) u, by rwa [Function.iterate_succ_apply'] at hn⟩

/-- On finite graphs, a spanning successor function is automatically a
permutation. Useful after contracting paths, where surjectivity follows from
the global orbit without a second local predecessor argument. -/
theorem OneOrbit.bijective {V : Type*} [Finite V] {next : V → V} (h : OneOrbit next) :
    Function.Bijective next :=
  ⟨Finite.injective_iff_surjective.mpr h.surjective, h.surjective⟩

/-- A finite closed route missing an outside vertex contradicts a spanning
orbit. The route need not be injective. -/
theorem OneOrbit.not_closed_enumeration {V : Type*} {next : V → V}
    (h : OneOrbit next) {n : Nat} (route : Fin (n + 1) → V) (outside : V)
    (hout : ∀ i, outside ≠ route i)
    (hstep : ∀ i, next (route i) = route (finRotate _ i)) : False := by
  have hp := h.closed_spans (P := fun v => ∃ i, route i = v) ⟨0, rfl⟩ (by
    rintro v ⟨i, rfl⟩
    exact ⟨finRotate _ i, (hstep i).symm⟩) outside
  obtain ⟨i, hi⟩ := hp
  exact hout i hi.symm

theorem OneOrbit.not_period_two {V : Type*} [Fintype V] {next : V → V}
    (h : OneOrbit next) (h3 : 3 ≤ Fintype.card V) (v : V) : next (next v) ≠ v := by
  classical
  intro h2
  have hall : ∀ w, w = v ∨ w = next v :=
    h.closed_spans (P := fun w => w = v ∨ w = next v) (Or.inl rfl) (by
      intro w hw
      rcases hw with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl h2)
  have hs : (Finset.univ : Finset V) ⊆ {v, next v} := by
    intro w _
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hall w
  have hc := Finset.card_le_card hs
  have hp := Finset.card_insert_le v ({next v} : Finset V)
  simp only [Finset.card_univ, Finset.card_singleton] at hc hp
  omega

/-- On at least three vertices, a spanning successor permutation is exactly
a Hamiltonian cycle of the underlying undirected graph. -/
theorem hamiltonianCycle_iff_oneOrbit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h3 : 3 ≤ Fintype.card V) :
    (∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle) ↔
      ∃ next : V ≃ V, OneOrbit next ∧ ∀ v, G.Adj v (next v) := by
  constructor
  · intro hc
    obtain ⟨_, _, cycle⟩ := hc
    obtain ⟨e, he⟩ := enumerateCycle cycle
    let next : V ≃ V := e.symm.trans ((finRotate _).trans e)
    have hstep : ∀ i, next (e i) = e (finRotate _ i) := by
      intro i
      simp [next]
    refine ⟨next, (oneOrbit_finRotate _).transport e hstep, ?_⟩
    intro v
    simpa [next] using he (e.symm v)
  · rintro ⟨next, horbit, hadj⟩
    classical
    let H : SimpleGraph V := SimpleGraph.fromRel (fun u v => next u = v)
    have hHG : H ≤ G := by
      intro u v huv
      rcases (SimpleGraph.fromRel_adj _ _ _).mp huv with ⟨_, h | h⟩
      · exact h ▸ hadj u
      · exact h ▸ (hadj v).symm
    have hstep : ∀ v, H.Adj v (next v) := by
      intro v
      exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨(hadj v).ne, Or.inl rfl⟩
    have hnb : ∀ v, H.neighborSet v = {next.symm v, next v} := by
      intro v
      ext w
      change H.Adj v w ↔ w = next.symm v ∨ w = next v
      constructor
      · intro hw
        rcases ((SimpleGraph.fromRel_adj _ _ _).mp hw).2 with hw | hw
        · exact Or.inr hw.symm
        · exact Or.inl (next.eq_symm_apply.mpr hw)
      · rintro (rfl | rfl)
        · simpa using (hstep (next.symm v)).symm
        · exact hstep v
    have hcyc : H.IsCycles := by
      intro v _
      rw [hnb]
      apply Set.ncard_pair
      intro heq
      have hp := congrArg next heq
      simp only [Equiv.apply_symm_apply] at hp
      exact horbit.not_period_two h3 v hp.symm
    have hreach : ∀ n v, H.Reachable v ((next^[n]) v) := by
      intro n
      induction n with
      | zero => intro v; exact Reachable.refl _
      | succ n ih =>
        intro v
        rw [Function.iterate_succ_apply']
        exact (ih v).trans (hstep _).reachable
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hconn : H.Connected := by
      constructor
      intro u v
      obtain ⟨n, rfl⟩ := horbit u v
      exact hreach n u
    exact exists_isHamiltonianCycle_mono hHG
      (exists_isHamiltonianCycle_of_isCycles hcyc hconn)

end GridHardness
