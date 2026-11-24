/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatVariables

/-!
# SAT XOR Interface

Exact incident-edge interface of every occurrence XOR in the concrete SAT
graph, including exclusion of a spurious link from an occurrence to itself.
-/

@[expose] public section

namespace GridHardness.PlanarSatAssembly

private theorem zip_shift_no_diagonal {A B : Type*} (f g : A → B)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (l : List A) (hn : l.Nodup) (o : A) (a b : B)
    (ha : a ≠ f o) (hb : b ≠ g o) :
    (f o, g o) ∉ (a :: l.map f).zip (l.map g ++ [b]) := by
  induction l generalizing a with
  | nil => simp [ha.symm]
  | cons c l ih =>
    simp only [List.map_cons, List.cons_append, List.zip_cons_cons, List.mem_cons]
    rintro (he | he)
    · exact ha (congrArg Prod.fst he).symm
    · by_cases hc : c = o
      · subst c
        have hm := (List.of_mem_zip he).2
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
          exact (List.nodup_cons.mp hn).1 ((hg he) ▸ hp)
        · exact hb (List.mem_singleton.mp hm).symm
      · exact ih (List.nodup_cons.mp hn).2 (f c) (fun h => hc (hf h)) he

theorem variableChain_no_self {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) : (xor o 0, xor o 3) ∉ variableChain φ v := by
  apply zip_shift_no_diagonal (fun p => xor p 0) (fun p => xor p 3)
    (fun _ _ h => by simpa [xor] using h)
    (fun _ _ h => by simpa [xor] using h)
    (occurrencesOf φ v) (occurrencesOf_nodup φ v) o
  · simp [var, xor]
  · simp [var, xor]

/-- On a single occurrence, the induced directed graph consists of exactly
the ten original XOR arcs. This also handles repeated literals. -/
theorem xor_internal_iff {n m : Nat} (φ : Formula n m)
    (o : Occurrence m) (i j : Fin 8) :
    Adj φ (xor o i) (xor o j) ↔ ∃ e : Fin 10, XorGadget.arc e = (i, j) := by
  constructor
  · intro h
    simp only [Adj, edges, List.mem_append] at h
    rcases h with (((hs | hb) | hv) | hc) | hx
    · simp [xor, sent] at hs
    · exact False.elim (backbone_no_xor_source o i _ hb)
    · obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hv
      rcases List.mem_cons.mp hv with hv | hv
      · simp [xor, var] at hv
      · have hi := variableChain_xor_source φ v o i _ hv
        have hj := variableChain_xor_target φ v o j _ hv
        subst i
        subst j
        exact False.elim (variableChain_no_self φ v o hv)
    · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hc
      simp [clauseEdges, xor, clause] at hc
    · obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp hp with hp | hp
      · simp [clauseLinks, xor, clause] at hp
      · obtain ⟨e, _, he⟩ := List.mem_map.mp hp
        have hs := congrArg Prod.fst he
        have ht := congrArg Prod.snd he
        simp only [xor, Sum.inr.injEq, Prod.mk.injEq] at hs ht
        exact ⟨e, Prod.ext hs.2 ht.2⟩
  · rintro ⟨e, he⟩
    unfold Adj edges
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨o, mem_occurrences o, List.mem_append_right _ ?_⟩
    apply List.mem_map.mpr
    exact ⟨e, List.mem_finRange e, by simp [he]⟩

abbrev Outside (n m : Nat) := Fin 3 ⊕ ((Fin n × Bool) ⊕ (Fin m × Fin 12))

def outsideVertex {n m : Nat} : Outside n m → Vertex n m
  | .inl i => sent i
  | .inr (.inl p) => var p.1 p.2
  | .inr (.inr p) => clause p.1 p.2

theorem outside_ne_xor {n m : Nat} (a : Outside n m) (o : Occurrence m) (j : Fin 8) :
    outsideVertex a ≠ xor o j := by
  rcases a with i | (⟨v, b⟩ | ⟨c, k⟩) <;> simp [outsideVertex, sent, var, clause, xor]

theorem outside_to_xor_port {n m : Nat} (φ : Formula n m)
    (a : Outside n m) (o : Occurrence m) (j : Fin 8)
    (h : Adj φ (outsideVertex a) (xor o j)) : j = 3 ∨ j = 4 := by
  by_contra hn
  obtain ⟨e, _, he⟩ := xor_incoming φ o j
    (fun hj => hn (Or.inl hj)) (fun hj => hn (Or.inr hj)) _ h
  exact outside_ne_xor a o _ he

theorem xor_to_outside_port {n m : Nat} (φ : Formula n m)
    (o : Occurrence m) (i : Fin 8) (a : Outside n m)
    (h : Adj φ (xor o i) (outsideVertex a)) : i = 0 ∨ i = 7 := by
  by_contra hn
  obtain ⟨e, _, he⟩ := xor_outgoing φ o i
    (fun hi => hn (Or.inl hi)) (fun hi => hn (Or.inr hi)) _ h
  exact outside_ne_xor a o _ he

theorem xor_link_ports {n m : Nat} (φ : Formula n m)
    (o p : Occurrence m) (hneq : o ≠ p) (i j : Fin 8)
    (h : Adj φ (xor o i) (xor p j)) : (i = 0 ∨ i = 7) ∧ (j = 3 ∨ j = 4) := by
  constructor
  · by_contra hn
    obtain ⟨e, _, he⟩ := xor_outgoing φ o i
      (fun hi => hn (Or.inl hi)) (fun hi => hn (Or.inr hi)) _ h
    simp only [xor, Sum.inr.injEq, Prod.mk.injEq] at he
    exact hneq he.1.symm
  · by_contra hn
    obtain ⟨e, _, he⟩ := xor_incoming φ p j
      (fun hj => hn (Or.inl hj)) (fun hj => hn (Or.inr hj)) _ h
    simp only [xor, Sum.inr.injEq, Prod.mk.injEq] at he
    exact hneq he.1

end GridHardness.PlanarSatAssembly
