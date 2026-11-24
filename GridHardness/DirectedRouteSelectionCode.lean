/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedRouteLookupCode

/-!
# Directed Route Selection Code

Canonical first-match normalization of arbitrary directed-route catalogues.
Every key keeps its first available route, even when the input contains distinct
routes for the same endpoints. Every chosen route is an original record.
-/

@[expose] public section

namespace GridHardness.DirectedRouteSelectionCode
open CliffordComplexity GridProblems GridProblems.GridCode DirectedRouteLookupCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Existence of a key suffices for selection to return an actual record.
No functional-key assumption is needed. -/
theorem lookup_mem (rs : RecordsTy.denote) (q : KeyTy.denote)
    (h : ∃ r ∈rs, r.1 =q) : (q,lookup rs q)∈rs := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    rcases r with ⟨k,p⟩
    by_cases hk : k=q
    · subst k
      simp [lookup]
    · rw [lookup,ite_eq_right hk]
      apply List.mem_cons_of_mem
      apply ih
      obtain ⟨r,hr,he⟩ := h
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact False.elim (hk he)
      · exact ⟨r,hr,he⟩

theorem code_lookup_mem (rs : RecordsTy.denote) (q : KeyTy.denote)
    (h : ∃ r ∈rs, r.1 =q) : (q,DirectedRouteLookupCode.code.eval (rs,q))∈rs := by
  rw [DirectedRouteLookupCode.code_eval]
  exact lookup_mem rs q h

/-- Replace each route by the first route at its existing endpoint key. -/
def normalize (rs : RecordsTy.denote) : RecordsTy.denote :=
  rs.map (fun r => (r.1,lookup rs r.1))

def record : Code (.pair RecordsTy RecordTy) RecordTy :=
  .pair (.comp .snd .fst)
    (.comp (.pair .fst (.comp .snd .fst)) DirectedRouteLookupCode.code)

def code : Code RecordsTy RecordsTy := .comp (.pair .id .id) (.listMapEnv record)

theorem code_eval (rs : RecordsTy.denote) : code.eval rs=normalize rs := by
  change rs.map (fun r => (r.1,DirectedRouteLookupCode.code.eval (rs,r.1)))=_
  unfold normalize
  exact List.map_congr_left (fun r _ => congrArg (Prod.mk r.1) (DirectedRouteLookupCode.code_eval rs r.1))

theorem mem_normalize (rs : RecordsTy.denote) (r : RecordTy.denote) :
    r∈normalize rs ↔ (∃ s∈rs,s.1=r.1) ∧ r.2=lookup rs r.1 := by
  unfold normalize
  rw [List.mem_map]
  constructor
  · rintro ⟨s,hs,he⟩
    have hk := congrArg Prod.fst he
    have hp := congrArg Prod.snd he
    change s.1=r.1 at hk
    change lookup rs s.1=r.2 at hp
    exact ⟨⟨s,hs,hk⟩,by simpa only [hk] using hp.symm⟩
  · rintro ⟨⟨s,hs,hk⟩,hp⟩
    exact ⟨s,hs,Prod.ext hk (by simpa only [hk] using hp.symm)⟩

/-- The normalized catalogue draws every route from the original catalogue. -/
theorem normalize_subset (rs : RecordsTy.denote) : normalize rs ⊆ rs := by
  intro r hr
  obtain ⟨hm,hp⟩ := (mem_normalize rs r).mp hr
  have h := lookup_mem rs r.1 hm
  simpa only [← hp,Prod.eta] using h

theorem keys (rs : RecordsTy.denote) : (normalize rs).map Prod.fst=rs.map Prod.fst := by
  simp only [normalize,List.map_map,Function.comp_def]

theorem length (rs : RecordsTy.denote) : (normalize rs).length=rs.length :=
  List.length_map (as:=rs) (fun r : RecordTy.denote => (r.1,lookup rs r.1))

theorem functional (rs : RecordsTy.denote) : Functional (normalize rs) := by
  intro r hr s hs he
  have h := (mem_normalize rs r).mp hr
  have j := (mem_normalize rs s).mp hs
  rw [h.2,j.2,he]

theorem covers (rs : RecordsTy.denote) (q : KeyTy.denote) :
    (∃r∈normalize rs,r.1=q) ↔ ∃r∈rs,r.1=q := by
  constructor
  · rintro ⟨r,hr,he⟩
    exact ⟨r,normalize_subset rs hr,he⟩
  · rintro ⟨r,hr,he⟩
    exact ⟨(r.1,lookup rs r.1),List.mem_map.mpr ⟨r,hr,rfl⟩,he⟩

theorem selected_mem_normalize (rs : RecordsTy.denote) (q : KeyTy.denote)
    (h : ∃ r∈rs, r.1 =q) : (q,lookup rs q)∈normalize rs :=
  (mem_normalize rs _).mpr ⟨h,rfl⟩

/-- Lookup is unchanged, including at absent keys. -/
theorem lookup_normalize (rs : RecordsTy.denote) (q : KeyTy.denote) :
    lookup (normalize rs) q=lookup rs q := by
  by_cases h : ∃r∈rs,r.1=q
  · exact lookup_eq_of_mem _ _ _ (selected_mem_normalize rs q h) (functional rs)
  · rw [lookup_missing rs q (by simpa only [not_exists,not_and] using h)]
    apply lookup_missing
    intro r hr he
    exact h ⟨r,normalize_subset rs hr,he⟩

theorem idempotent (rs : RecordsTy.denote) : normalize (normalize rs)=normalize rs := by
  unfold normalize
  rw [List.map_map]
  apply List.map_congr_left
  intro r _
  exact congrArg (Prod.mk r.1) (lookup_normalize rs r.1)

/-- Already functional catalogues are unchanged as lists. -/
theorem normalize_eq_self (rs : RecordsTy.denote) (h : Functional rs) : normalize rs=rs := by
  unfold normalize
  calc
    rs.map (fun r => (r.1,lookup rs r.1)) = rs.map id := by
      apply List.map_congr_left
      intro r hr
      exact Prod.ext rfl (lookup_eq_of_mem rs r.1 r.2 (by simpa using hr) h)
    _ = rs := List.map_id rs

theorem mem_code (rs : RecordsTy.denote) (r : RecordTy.denote) :
    r∈code.eval rs ↔ (∃s∈rs,s.1=r.1) ∧ r.2=DirectedRouteLookupCode.code.eval (rs,r.1) := by
  rw [code_eval,mem_normalize,DirectedRouteLookupCode.code_eval]

theorem code_length (rs : RecordsTy.denote) : (code.eval rs).length=rs.length := by
  rw [code_eval,length]

end GridHardness.DirectedRouteSelectionCode
