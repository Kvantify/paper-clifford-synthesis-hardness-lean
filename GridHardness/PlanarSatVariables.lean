/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatXor

/-!
# Planar SAT Variables

Enumerate variable occurrences and identify the source and target of each chain edge.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PlanarSatAssembly

@[simp] theorem mem_occurrences {m : Nat} (o : Occurrence m) : o ∈ occurrences m := by
  rcases o with ⟨c,j⟩
  simp [occurrences]

@[simp] theorem mem_occurrencesOf {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) : o ∈ occurrencesOf φ v ↔ φ o.1 o.2 = v := by
  simp [occurrencesOf]

theorem occurrences_nodup (m : Nat) : (occurrences m).Nodup := by
  rw [occurrences,List.nodup_flatMap]
  constructor
  · intro c _
    exact (List.nodup_finRange 3).map (fun a b h => (Prod.mk.inj h).2)
  · apply (List.nodup_finRange m).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro p hp hq
    simp only [List.mem_map] at hp hq
    obtain ⟨i,_,hi⟩ := hp
    obtain ⟨j,_,hj⟩ := hq
    exact hab (congrArg Prod.fst (hi.trans hj.symm))

theorem occurrencesOf_nodup {n m : Nat} (φ : Formula n m) (v : Fin n) :
    (occurrencesOf φ v).Nodup := (occurrences_nodup m).filter _

private theorem xor_all_injective {n m : Nat} (i : Fin 8) :
    Function.Injective (fun o : Occurrence m => xor (n := n) o i) := by
  intro a b h
  simpa [xor] using h

private theorem zip_target_unique {A B : Type*} {xs : List A} {ys : List B}
    (hn : xs.Nodup) {a : A} {b c : B} (hb : (a, b) ∈ xs.zip ys)
    (hc : (a, c) ∈ xs.zip ys) : b = c := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hb
  obtain ⟨j,hj,hf⟩ := List.getElem_of_mem hc
  rw [List.getElem_zip] at he hf
  have hij : i = j := hn.getElem_inj_iff.mp ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)
  subst j
  exact (congrArg Prod.snd he).symm.trans (congrArg Prod.snd hf)

private theorem zip_source_unique {A B : Type*} {xs : List A} {ys : List B}
    (hn : ys.Nodup) {a b : A} {c : B} (ha : (a, c) ∈ xs.zip ys)
    (hb : (b, c) ∈ xs.zip ys) : a = b := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
  obtain ⟨j,hj,hf⟩ := List.getElem_of_mem hb
  rw [List.getElem_zip] at he hf
  have hij : i = j := hn.getElem_inj_iff.mp ((congrArg Prod.snd he).trans (congrArg Prod.snd hf).symm)
  subst j
  exact (congrArg Prod.fst he).symm.trans (congrArg Prod.fst hf)

/-- Every occurrence port occurs only once as a source in its variable chain. -/
theorem variableChain_target_unique {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b c : Vertex n m} (hb : (a, b) ∈ variableChain φ v)
    (hc : (a, c) ∈ variableChain φ v) : b = c := by
  apply zip_target_unique (ys := _) ?_ hb hc
  apply List.nodup_cons.mpr
  constructor
  · simp [var,xor]
  · exact (occurrencesOf_nodup φ v).map (xor_all_injective 0)

/-- Every occurrence port occurs only once as a target in its variable chain. -/
theorem variableChain_source_unique {n m : Nat} (φ : Formula n m) (v : Fin n)
    {a b c : Vertex n m} (ha : (a, c) ∈ variableChain φ v)
    (hb : (b, c) ∈ variableChain φ v) : a = b := by
  apply zip_source_unique (xs := _) ?_ ha hb
  apply List.nodup_append.mpr
  refine ⟨(occurrencesOf_nodup φ v).map (xor_all_injective 3),by simp,?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst b
  rw [hb] at ha
  simpa [var,xor] using ha

theorem variableChain_xor_source_owner {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) (w : Vertex n m)
    (h : (xor o 0, w) ∈ variableChain φ v) : φ o.1 o.2 = v := by
  have hm := (List.of_mem_zip h).1
  simp only [List.mem_cons,List.mem_map] at hm
  rcases hm with hm | ⟨p,hp,he⟩
  · simp [xor,var] at hm
  · have : p = o := xor_all_injective 0 he
    subst p
    exact (mem_occurrencesOf φ v o).mp hp

theorem variableChain_xor_target_owner {n m : Nat} (φ : Formula n m) (v : Fin n)
    (o : Occurrence m) (w : Vertex n m)
    (h : (w, xor o 3) ∈ variableChain φ v) : φ o.1 o.2 = v := by
  have hm := (List.of_mem_zip h).2
  simp only [List.mem_append,List.mem_map,List.mem_singleton] at hm
  rcases hm with ⟨p,hp,he⟩ | hm
  · have : p = o := xor_all_injective 3 he
    subst p
    exact (mem_occurrencesOf φ v o).mp hp
  · simp [xor,var] at hm

/-- The only edges leaving the left exit are its internal edge and its variable link. -/
theorem xor_zero_outgoing {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (w : Vertex n m) (h : Adj φ (xor o 0) w) :
    w = xor o 1 ∨ (xor o 0,w) ∈ variableChain φ (φ o.1 o.2) := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor,sent] at hs
  · exact False.elim (backbone_no_xor_source o 0 w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor,var] at hv
    · have he := variableChain_xor_source_owner φ v o w hv
      exact Or.inr (he ▸ hv)
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges,xor,clause] at hc
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp [clauseLinks,xor,clause] at ha
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor,Sum.inr.injEq,Prod.mk.injEq] at hsrc
      rcases hsrc with ⟨rfl,hsrc⟩
      have hedge : ∀ e : Fin 10, (XorGadget.arc e).1 = 0 → (XorGadget.arc e).2 = 1 := by decide
      rw [hedge e hsrc] at hdst
      exact Or.inl hdst.symm

/-- The left entry receives its internal edge or the unique preceding variable link. -/
theorem xor_three_incoming {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (w : Vertex n m) (h : Adj φ w (xor o 3)) :
    w = xor o 2 ∨ (w,xor o 3) ∈ variableChain φ (φ o.1 o.2) := by
  simp only [Adj,edges,List.mem_append] at h
  rcases h with (((hs | hb) | hv) | hc) | hx
  · simp [xor,sent] at hs
  · exact False.elim (backbone_no_xor_target o 3 w hb)
  · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with hv | hv
    · simp [xor,var] at hv
    · have he := variableChain_xor_target_owner φ v o w hv
      exact Or.inr (he ▸ hv)
  · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
    simp [clauseEdges,xor,clause] at hc
  · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp ha with ha | ha
    · simp [clauseLinks,xor,clause] at ha
    · obtain ⟨e,_,he⟩ := List.mem_map.mp ha
      have hsrc := congrArg Prod.fst he
      have hdst := congrArg Prod.snd he
      simp only [xor,Sum.inr.injEq,Prod.mk.injEq] at hdst
      rcases hdst with ⟨rfl,hdst⟩
      have hedge : ∀ e : Fin 10, (XorGadget.arc e).2 = 3 → (XorGadget.arc e).1 = 2 := by decide
      rw [hedge e hdst] at hsrc
      exact Or.inl hsrc.symm

open PlanarSatXor XorGadget

private theorem left_exit_not_internal {n m : Nat} (next : Equiv.Perm (Vertex n m))
    (o : Occurrence m) (h : selection next (xor o) = leftRoute) :
    next (xor o 0) ≠ xor o 1 := by
  have he := congrFun h 0
  simpa [selection,arc,leftRoute] using he

private theorem left_entry_not_internal {n m : Nat} (next : Equiv.Perm (Vertex n m))
    (o : Occurrence m) (h : selection next (xor o) = leftRoute) :
    next (xor o 2) ≠ xor o 3 := by
  have he := congrFun h 3
  simpa [selection,arc,leftRoute] using he

private theorem right_exit_internal {n m : Nat} (next : Equiv.Perm (Vertex n m))
    (o : Occurrence m) (h : selection next (xor o) = rightRoute) :
    next (xor o 0) = xor o 1 := by
  have he := congrFun h 0
  simpa [selection,arc,rightRoute] using he

private theorem right_entry_internal {n m : Nat} (next : Equiv.Perm (Vertex n m))
    (o : Occurrence m) (h : selection next (xor o) = rightRoute) :
    next (xor o 2) = xor o 3 := by
  have he := congrFun h 3
  simpa [selection,arc,rightRoute] using he

/-- Consecutive occurrences on a variable chain make the same XOR choice.
Both directions follow from actual port-edge uniqueness and permutation injectivity. -/
theorem variable_link_same_choice {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (ho : OneOrbit next)
    (ha : ∀ v, Adj φ v (next v)) (v : Fin n) (o p : Occurrence m)
    (hedge : (xor o 0, xor p 3) ∈ variableChain φ v) :
    selection next (xor o) = selection next (xor p) := by
  have hov := variableChain_xor_source_owner φ v o (xor p 3) hedge
  have hpv := variableChain_xor_target_owner φ v p (xor o 0) hedge
  rcases assembly_selection φ next ho ha o with hol | hor <;>
    rcases assembly_selection φ next ho ha p with hpl | hpr
  · exact hol.trans hpl.symm
  · have he := xor_zero_outgoing φ o _ (ha (xor o 0))
    have hm := he.resolve_left (left_exit_not_internal next o hol)
    rw [hov] at hm
    have hn := variableChain_target_unique φ v hm hedge
    have heq := next.injective (hn.trans (right_entry_internal next p hpr).symm)
    simp [xor] at heq
  · have hap : Adj φ (next.symm (xor p 3)) (xor p 3) := by
      simpa using ha (next.symm (xor p 3))
    have he := xor_three_incoming φ p _ hap
    have hni : next.symm (xor p 3) ≠ xor p 2 := by
      intro heq
      have hh := congrArg next heq
      simp only [Equiv.apply_symm_apply] at hh
      exact left_entry_not_internal next p hpl hh.symm
    have hm := he.resolve_left hni
    rw [hpv] at hm
    have hn := variableChain_source_unique φ v hm hedge
    have hh := congrArg next hn
    simp only [Equiv.apply_symm_apply,right_exit_internal next o hor] at hh
    simp [xor] at hh
  · exact hor.trans hpr.symm

/-- The constructor contains the link between every two consecutive occurrences. -/
theorem variableChain_consecutive {n m : Nat} (φ : Formula n m) (v : Fin n)
    (i : Nat) (hi : i +1 < (occurrencesOf φ v).length) :
    (xor (occurrencesOf φ v)[i] 0,xor (occurrencesOf φ v)[i+1] 3) ∈ variableChain φ v := by
  apply List.mem_iff_getElem.mpr
  refine ⟨i+1,by rw [variableChain_length]; omega,?_⟩
  simp only [variableChain,List.getElem_zip,List.getElem_cons_succ]
  rw [List.getElem_append_left (by simpa using hi)]
  simp only [List.getElem_map]

/-- All occurrences of a variable, wherever they occur in clauses, make the same choice. -/
theorem variable_same_choice {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (ho : OneOrbit next)
    (ha : ∀ v, Adj φ v (next v)) (v : Fin n) (o p : Occurrence m)
    (hox : φ o.1 o.2 = v) (hpx : φ p.1 p.2 = v) :
    selection next (xor o) = selection next (xor p) := by
  have hom := (mem_occurrencesOf φ v o).mpr hox
  have hpm := (mem_occurrencesOf φ v p).mpr hpx
  obtain ⟨i,hi,hio⟩ := List.getElem_of_mem hom
  obtain ⟨j,hj,hjp⟩ := List.getElem_of_mem hpm
  have h0 : 0 < (occurrencesOf φ v).length := by omega
  have hh : ∀ k (hk : k < (occurrencesOf φ v).length),
      selection next (xor (occurrencesOf φ v)[k]) =
        selection next (xor (occurrencesOf φ v)[0]) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hs := variable_link_same_choice φ next ho ha v
        (occurrencesOf φ v)[k] (occurrencesOf φ v)[k+1]
        (variableChain_consecutive φ v k hk)
      exact hs.symm.trans (ih (by omega))
  have hei := hh i hi
  have hej := hh j hj
  rw [hio] at hei
  rw [hjp] at hej
  exact hei.trans hej.symm

/-- Read a truth assignment from the actual successor; unused variables are false. -/
def extractedAssignment {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (v : Fin n) : Bool :=
  (occurrencesOf φ v).any (fun o => decide (selection next (xor o) = leftRoute))

/-- Every occurrence's left route is exactly the extracted variable's truth value. -/
theorem extractedAssignment_spec {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (ho : OneOrbit next)
    (ha : ∀ v, Adj φ v (next v)) (o : Occurrence m) :
    extractedAssignment φ next (φ o.1 o.2) = true ↔
      selection next (xor o) = leftRoute := by
  simp only [extractedAssignment,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,hs⟩
    have hpx := (mem_occurrencesOf φ (φ o.1 o.2) p).mp hp
    exact (variable_same_choice φ next ho ha (φ o.1 o.2) o p rfl hpx).trans hs
  · intro h
    exact ⟨o,(mem_occurrencesOf φ (φ o.1 o.2) o).mpr rfl,h⟩

end GridHardness.PlanarSatAssembly
