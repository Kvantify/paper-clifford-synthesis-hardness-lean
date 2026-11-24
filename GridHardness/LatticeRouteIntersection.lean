/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteSubdivision
public import GridHardness.LatticeRouteDirections

/-!
# Lattice Route Intersection

Integer subdivision preserves endpoint-only intersections of simple
lattice paths. The lower bound of three vertices excludes sharing an entire
unit edge while meeting only at endpoints.
-/

public section

namespace GridHardness.LatticeSubdivision
open CliffordSynthesis
open LatticeRouteDirections (Endpoint)
set_option autoImplicit false

/-- Every route edge occurs at two consecutive list indices. -/
theorem edges_index (l : List Point) (a b : Point) (hab : (a, b) ∈edges l) :
    ∃ i, ∃ hi : i+1<l.length,
      l[i]'(by omega)=a ∧ l[i+1]'hi=b := by
  induction l with
  | nil => simp [edges] at hab
  | cons c l ih =>
    cases l with
    | nil => simp [edges] at hab
    | cons d l =>
      rcases List.mem_cons.mp hab with he | he
      · cases he
        exact ⟨0,by simp, rfl,rfl⟩
      · obtain ⟨i,hi,ha,hb⟩ := ih he
        refine ⟨i+1,by simpa using hi,?_,?_⟩
        · simpa using ha
        · simpa [Nat.add_assoc] using hb

/-- In a simple path with at least three vertices, an edge cannot join the
two path endpoints. -/
theorem edge_not_both_endpoints (l : List Point) (hl : 3 ≤l.length)
    (hn : l.Nodup) (a b : Point) (hab : (a, b) ∈edges l) :
    ¬(Endpoint l a ∧ Endpoint l b) := by
  obtain ⟨i,hi,ha,hb⟩ := edges_index l a b hab
  have hinj := List.nodup_iff_injective_getElem.mp hn
  have endpoint_index (k : Nat) (hk : k<l.length) (v : Point)
      (hv : l[k]'hk=v) (he : Endpoint l v) : k=0 ∨ k=l.length-1 := by
    rcases he with he | he
    · rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at he
      have hf := congrArg Fin.val
        (hinj (a₁ := ⟨k,hk⟩) (a₂ := ⟨0,by omega⟩)
          (hv.trans (Option.some.inj he).symm))
      exact Or.inl hf
    · rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at he
      have hf := congrArg Fin.val
        (hinj (a₁ := ⟨k,hk⟩) (a₂ := ⟨l.length-1,by omega⟩)
          (hv.trans (Option.some.inj he).symm))
      exact Or.inr hf
  rintro ⟨hea,heb⟩
  have hia := endpoint_index i (by omega) a ha hea
  have hib := endpoint_index (i+1) hi b hb heb
  omega

/-- Endpoint-only intersections survive dilation and subdivision. Simplicity
and the three-vertex bound are needed for only one of the two original paths. -/
theorem subdivide_intersection (s : Nat) (hs : 0 <s) (l m : List Point)
    (hl : 3 ≤l.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hinter : ∀ v, v ∈l → v ∈m → Endpoint l v ∧ Endpoint m v)
    (q : Point) (hql : q ∈subdivide s l) (hqm : q ∈subdivide s m) :
    ∃ v, Endpoint l v ∧ Endpoint m v ∧ q=scale s v := by
  rcases (subdivide_mem s l q).mp hql with ⟨a,ha,haq⟩ | ⟨a,b,hab,t,ht,htq⟩
  · have hal : a∈l := List.mem_of_mem_getLast? (by rw [ha]; simp)
    have ham : a∈m := (scale_mem_subdivide_iff s hs m hcm a).mp (haq ▸ hqm)
    exact ⟨a,(hinter a hal ham).1,(hinter a hal ham).2,haq.symm⟩
  rcases (subdivide_mem s m q).mp hqm with ⟨c,hc,hcq⟩ | ⟨c,d,hcd,r,hr,hrq⟩
  · have hcm' : c∈m := List.mem_of_mem_getLast? (by rw [hc]; simp)
    have hcl' : c∈l := (scale_mem_subdivide_iff s hs l hcl c).mp (hcq ▸ hql)
    exact ⟨c,(hinter c hcl' hcm').1,(hinter c hcl' hcm').2,hcq.symm⟩
  obtain ⟨hal,hbl⟩ := edges_mem_vertices l a b hab
  obtain ⟨hcm',hdm⟩ := edges_mem_vertices m c d hcd
  have hdirect : ¬(a=c ∧ b=d) := by
    rintro ⟨hac,hbd⟩
    exact edge_not_both_endpoints l hl hn a b hab
      ⟨(hinter a hal (by simpa [hac] using hcm')).1,
       (hinter b hbl (by simpa [hbd] using hdm)).1⟩
  have hreverse : ¬(a=d ∧ b=c) := by
    rintro ⟨had,hbc⟩
    exact edge_not_both_endpoints l hl hn a b hab
      ⟨(hinter a hal (by simpa [had] using hdm)).1,
       (hinter b hbl (by simpa [hbc] using hcm')).1⟩
  obtain ⟨v,hvl,hvm,hv⟩ := interpolate_intersection s hs
    (edges_unit l hcl a b hab) (edges_unit m hcm c d hcd) hdirect hreverse
    (Nat.le_of_lt ht) (Nat.le_of_lt hr) (htq.trans hrq.symm)
  have hvL : v∈l := hvl.elim (fun h => h ▸ hal) (fun h => h ▸ hbl)
  have hvM : v∈m := hvm.elim (fun h => h ▸ hcm') (fun h => h ▸ hdm)
  exact ⟨v,(hinter v hvL hvM).1,(hinter v hvL hvM).2,htq.symm.trans hv⟩

/-- Each original endpoint remains the corresponding scaled endpoint. -/
theorem subdivide_endpoint (s : Nat) (hs : 0 <s) (l : List Point) (v : Point)
    (hv : Endpoint l v) : Endpoint (subdivide s l) (scale s v) := by
  rcases hv with hv | hv
  · apply Or.inl
    rw [subdivide_head s hs,hv]
    rfl
  · apply Or.inr
    rw [subdivide_getLast,hv]
    rfl

/-- The subdivided routes still meet only at endpoints of both routes. -/
theorem subdivide_endpoint_intersection (s : Nat) (hs : 0 <s) (l m : List Point)
    (hl : 3 ≤l.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hinter : ∀ v, v ∈l → v ∈m → Endpoint l v ∧ Endpoint m v)
    (q : Point) (hql : q ∈subdivide s l) (hqm : q ∈subdivide s m) :
    Endpoint (subdivide s l) q ∧ Endpoint (subdivide s m) q := by
  obtain ⟨v,hvl,hvm,rfl⟩ := subdivide_intersection s hs l m hl hn hcl hcm hinter q hql hqm
  exact ⟨subdivide_endpoint s hs l v hvl,subdivide_endpoint s hs m v hvm⟩

end GridHardness.LatticeSubdivision
