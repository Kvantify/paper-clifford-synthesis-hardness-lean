/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCodeLists

/-!
# Directed Route Lookup Code

Certified lookup of a directed geometric route in an explicit catalogue.
The key is the ordered source/target pair of binary vertex identifiers. The
first matching record is selected; absence gives the empty route. Exact
selection and order independence under functional endpoint keys are proved
without assuming that construction of the catalogue is already certified.
-/

@[expose] public section

namespace GridHardness.DirectedRouteLookupCode
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev KeyTy := Ty.pair .nat .nat
abbrev RecordTy := Ty.pair KeyTy CycleInputTy
abbrev RecordsTy := Ty.list RecordTy
abbrev InputTy := Ty.pair RecordsTy KeyTy

/-- The reference first-match lookup, including its total missing-key case. -/
def lookup : RecordsTy.denote → KeyTy.denote → CycleInputTy.denote
  | [], _ => []
  | (k,r)::rs, q => if k=q then r else lookup rs q

def matching : Code InputTy RecordsTy :=
  .comp (.pair .snd .fst)
    (Code.filterEnv (.comp (.pair (.comp .snd .fst) .fst) Code.natPairEq))

theorem matching_eval (rs : RecordsTy.denote) (q : KeyTy.denote) :
    matching.eval (rs,q)=rs.filter (fun r => decide (r.1=q)) := by
  change (Code.filterEnv _).eval (q,rs)=_
  rw [filterEnv_eval]
  apply List.filter_congr
  intro r _
  rcases r with ⟨⟨u,v⟩,route⟩
  rcases q with ⟨a,b⟩
  simp [Code.eval, Code.natPairEq, Prod.mk.injEq]
  rfl

/-- The selected record as a zero- or one-element list, enabling exact
record-level statements as well as the flattened route output. -/
def selected : Code InputTy RecordsTy :=
  .comp (.pair matching (.const .nat 0)) Code.listNth

theorem selected_eval (rs : RecordsTy.denote) (q : KeyTy.denote) :
    selected.eval (rs,q)=(rs.filter (fun r => decide (r.1=q))).head?.toList := by
  change (Code.listNth (τ:=RecordTy)).eval (matching.eval (rs,q),0)=_
  rw [matching_eval, listNth_option]
  rw [← List.head?_eq_getElem?]

def code : Code InputTy CycleInputTy :=
  .comp selected (.comp (.listMap .snd) .listJoin)

theorem lookup_filter (rs : RecordsTy.denote) (q : KeyTy.denote) :
    (((rs.filter (fun r => decide (r.1=q))).head?.toList).map Prod.snd).flatten=
      lookup rs q := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨k,r⟩
    by_cases h : k=q
    · simp [h,lookup]
    · simpa [h,lookup] using ih

/-- Exact evaluation on every explicit catalogue, including malformed
catalogues with duplicate keys and missing-key queries. -/
theorem code_eval (rs : RecordsTy.denote) (q : KeyTy.denote) :
    code.eval (rs,q)=lookup rs q := by
  change ((selected.eval (rs,q)).map Prod.snd).flatten=_
  rw [selected_eval, lookup_filter]

theorem selected_mem (rs : RecordsTy.denote) (q : KeyTy.denote)
    (r : RecordTy.denote) (hr : r ∈selected.eval (rs, q)) : r∈rs ∧ r.1=q := by
  rw [selected_eval] at hr
  have hm : r∈rs.filter (fun a => decide (a.1=q)) :=
    List.mem_of_mem_head? (by simpa using hr)
  simpa using hm

/-- A catalogue's routes are a function of its ordered endpoint key.
Repeated identical records are allowed. -/
def Functional (rs : RecordsTy.denote) : Prop :=
  ∀r∈rs,∀s∈rs,r.1=s.1 → r.2=s.2

theorem lookup_eq_of_mem (rs : RecordsTy.denote) (q : KeyTy.denote)
    (route : CycleInputTy.denote) (hm : (q, route) ∈rs) (hf : Functional rs) :
    lookup rs q=route := by
  induction rs with
  | nil => simp at hm
  | cons r rs ih =>
    rcases r with ⟨k,r⟩
    by_cases hk : k=q
    · rw [lookup,ite_eq_left hk]
      exact hf (k,r) List.mem_cons_self (q,route) hm hk
    · rw [lookup,ite_eq_right hk]
      apply ih
      · rcases List.mem_cons.mp hm with he | he
        · exact False.elim (hk (congrArg Prod.fst he).symm)
        · exact he
      · intro a ha b hb he
        exact hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) he

theorem code_eq_of_mem (rs : RecordsTy.denote) (q : KeyTy.denote)
    (route : CycleInputTy.denote) (hm : (q, route) ∈rs) (hf : Functional rs) :
    code.eval (rs,q)=route := by
  rw [code_eval]
  exact lookup_eq_of_mem rs q route hm hf

theorem lookup_missing (rs : RecordsTy.denote) (q : KeyTy.denote)
    (h : ∀ r∈rs, r.1 ≠q) : lookup rs q=[] := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨k,r⟩
    rw [lookup,ite_eq_right (h (k,r) List.mem_cons_self)]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Any enumeration of the same functional route records produces exactly
the same result, independently of record order. -/
theorem code_order_independent (rs ts : RecordsTy.denote) (q : KeyTy.denote)
    (hf : Functional rs) (he : ∀ r, r∈rs ↔ r ∈ts) :
    code.eval (rs,q)=code.eval (ts,q) := by
  have ht : Functional ts := by
    intro a ha b hb hab
    exact hf a ((he a).mpr ha) b ((he b).mpr hb) hab
  by_cases hm : ∃r∈rs,r.1=q
  · obtain ⟨⟨k,r⟩,hr,hk⟩ := hm
    dsimp at hk
    subst k
    rw [code_eq_of_mem rs q r hr hf,code_eq_of_mem ts q r ((he _).mp hr) ht]
  · rw [code_eval,code_eval,lookup_missing,lookup_missing]
    · intro r hr hk
      exact hm ⟨r,(he r).mpr hr,hk⟩
    · intro r hr hk
      exact hm ⟨r,hr,hk⟩

end GridHardness.DirectedRouteLookupCode
