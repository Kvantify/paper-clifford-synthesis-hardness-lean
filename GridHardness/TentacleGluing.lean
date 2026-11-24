/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TentacleStrip

/-!
# Tentacle Gluing

Path splicing for two strips whose overlap is their joining edge.
-/

public section

namespace GridHardness
open SimpleGraph SimpleGraph.Walk
set_option backward.isDefEq.respectTransparency false

/-- At an internal vertex of degree two, a spanning path uses both available
edges. This is the path counterpart of the cycle forcing lemma. -/
theorem path_forced_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b v w : V}
    {p : G.Walk a b} (hp : p.IsHamiltonian) (hva : v ≠ a) (hvb : v ≠ b)
    (hd : G.degree v = 2) (hvw : G.Adj v w) : p.toSubgraph.Adj v w := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hp.mem_support v)
  have hi0 : i ≠ 0 := by intro h; subst i; simp only [Walk.getVert_zero] at hi; exact hva hi.symm
  have hilt : i < p.length := by
    by_contra h
    have hie : i = p.length := by omega
    subst i
    simp only [Walk.getVert_length] at hi
    exact hvb hi.symm
  have hpath : (p.toSubgraph.neighborSet v).ncard = 2 := by
    rw [← hi]
    exact hp.isPath.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hgraph : (G.neighborSet v).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, hd]
  have he : p.toSubgraph.Adj v w ↔ G.Adj v w := by
    refine SimpleGraph.Subgraph.adj_iff_of_neighborSet_equiv
      (show Nonempty _ from ?_).some (Set.toFinite _)
    rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _),
      ← Set.cast_ncard (Walk.finite_neighborSet_toSubgraph p), hpath, hgraph]
  exact he.mpr hvw

/-- Insert a route into one adjacent pair of another route. The finite order
statement exposes every visited vertex and is convenient for induction over
the list of geometric strips. -/
theorem insert_route_order {V : Type*} (R : V → V → Prop)
    (l m r : List V) (a b : V)
    (hchain : (l ++ a :: b :: r).IsChain R)
    (hroute : ((a :: m) ++ [b]).IsChain R)
    (hnod : (l ++ a :: b :: r).Nodup)
    (hmnod : ((a :: m) ++ [b]).Nodup)
    (hinter : ∀ v, v ∈ l ++ a :: b :: r → v ∈ (a :: m) ++ [b] → v = a ∨ v = b) :
    (l ++ a :: (m ++ b :: r)).IsChain R ∧ (l ++ a :: (m ++ b :: r)).Nodup ∧
      ∀ v, v ∈ l ++ a :: (m ++ b :: r) ↔
        v ∈ l ++ a :: b :: r ∨ v ∈ (a :: m) ++ [b] := by
  have hleft : (l ++ [a]).IsChain R := by
    apply List.IsChain.left_of_append (l₂ := b :: r)
    simpa using hchain
  have hright : (b :: r).IsChain R := hchain.right_of_append.of_cons
  have hfirst : (l ++ (a :: m) ++ [b]).IsChain R := by
    have h := hleft.append_overlap (l₃ := m ++ [b]) (by simpa using hroute) (by simp)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  have hnew : (l ++ a :: (m ++ b :: r)).IsChain R := by
    have h := hfirst.append_overlap (l₃ := r) (by simpa using hright) (by simp)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  have hm : m.Nodup := (List.nodup_append'.mp hmnod).1.of_cons
  have ha : a ∉ m := (List.nodup_cons.mp (List.nodup_append'.mp hmnod).1).1
  have hb : b ∉ m := by
    intro h
    exact (List.disjoint_left.mp (List.nodup_append'.mp hmnod).2.2
      (List.mem_cons_of_mem a h)) (by simp)
  have hdis : (l ++ a :: b :: r).Disjoint m := by
    rw [List.disjoint_left]
    intro v hv hvm
    rcases hinter v hv (by simp only [List.mem_append, List.mem_cons]; exact Or.inl (Or.inr hvm))
      with rfl | rfl
    · exact ha hvm
    · exact hb hvm
  have hperm : (l ++ a :: (m ++ b :: r)).Perm ((l ++ a :: b :: r) ++ m) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (List.perm_append_comm (l₁ := m) (l₂ := b :: r)).append_left (l ++ [a])
  refine ⟨hnew, hperm.nodup_iff.mpr (List.nodup_append'.mpr ⟨hnod, hm, hdis⟩), ?_⟩
  intro v
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Glue paths over a two-vertex overlap.  The first route ends by traversing
the shared edge. Removing its final vertex and appending the second route
visits the union exactly once. This is the combinatorial splice used when
a tentacle turns a corner. -/
theorem splice_overlap_edge {V : Type*} {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a c) (hp : p.IsPath) (hpn : ¬ p.Nil)
    (q : G.Walk p.penultimate b) (hq : q.IsPath)
    (hc : c ∈ q.support)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = c ∨ v = p.penultimate) :
    (p.dropLast.append q).IsPath ∧
      ∀ v, v ∈ (p.dropLast.append q).support ↔ v ∈ p.support ∨ v ∈ q.support := by
  let L := p.dropLast.support.dropLast
  have hpre : L ++ [p.penultimate, c] = p.support := by
    calc
      L ++ [p.penultimate, c] = (L ++ [p.penultimate]) ++ [c] := by simp
      _ = p.dropLast.support ++ [c] := by rw [Walk.dropLast_support_concat]
      _ = p.support := Walk.support_dropLast_concat hpn
  have hnod : (L ++ [p.penultimate, c]).Nodup := by rw [hpre]; exact hp.support_nodup
  have hL : L.Nodup := (List.nodup_append'.mp hnod).1
  have hsep : L.Disjoint [p.penultimate, c] := (List.nodup_append'.mp hnod).2.2
  have hdis : L.Disjoint q.support := by
    rw [List.disjoint_left]
    intro v hv hqv
    have hpv : v ∈ p.support := by rw [← hpre]; simp only [List.mem_append]; exact Or.inl hv
    have hends := hinter v hpv hqv
    exact (List.disjoint_left.mp hsep hv) (by simpa using hends.symm)
  have hs : (p.dropLast.append q).support = L ++ q.support :=
    Walk.support_append_eq_support_dropLast_append _ _
  constructor
  · rw [Walk.isPath_def, hs]
    exact List.nodup_append'.mpr ⟨hL, hq.support_nodup, hdis⟩
  · intro v
    rw [hs, ← hpre]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h | h) | h)
      · exact Or.inl h
      · subst v; exact Or.inr q.start_mem_support
      · subst v; exact Or.inr hc
      · exact Or.inr h

/-- If the two pieces together contain every vertex of the ambient graph,
the same splice is Hamiltonian. -/
theorem hamiltonian_splice_overlap_edge {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a c) (hp : p.IsPath) (hpn : ¬ p.Nil)
    (q : G.Walk p.penultimate b) (hq : q.IsPath)
    (hc : c ∈ q.support)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = c ∨ v = p.penultimate)
    (hcover : ∀ v, v ∈ p.support ∨ v ∈ q.support) :
    (p.dropLast.append q).IsHamiltonian := by
  obtain ⟨hpq, hmem⟩ := splice_overlap_edge p hp hpn q hq hc hinter
  exact hpq.isHamiltonian_of_mem (fun v => (hmem v).mpr (hcover v))

/-- Two complementary simple routes form a Hamiltonian cycle.  This is the
global closure step after inserting return routes into a cluster route. -/
theorem hamiltonianCycle_of_two_paths {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk b a) (hq : q.IsPath)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = a ∨ v = b)
    (hlength : 1 < p.length ∨ 1 < q.length)
    (hcover : ∀ v, v ∈ p.support ∨ v ∈ q.support) :
    (p.append q).IsHamiltonianCycle := by
  have ha : a ∉ p.support.tail := by
    have h := hp.support_nodup
    rw [← Walk.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have hb : b ∉ q.support.tail := by
    have h := hq.support_nodup
    rw [← Walk.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have hdis : p.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro v hvp hvq
    rcases hinter v (List.mem_of_mem_tail hvp) (List.mem_of_mem_tail hvq) with rfl | rfl
    · exact ha hvp
    · exact hb hvq
  have hc := hp.isCycle_append hq hdis hlength
  refine ⟨hc, hc.isPath_tail.isHamiltonian_of_mem ?_⟩
  intro v
  rw [Walk.support_tail_of_not_nil _ hc.not_nil]
  have hv : v ∈ (p.append q).support := (Walk.mem_support_append_iff _ _).mpr (hcover v)
  rw [← Walk.cons_tail_support, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact Walk.end_mem_tail_support hc.not_nil
  · exact hv

end GridHardness
