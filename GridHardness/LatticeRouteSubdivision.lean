/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeSubdivision

/-!
# Lattice Route Subdivision

Subdividing lattice routes after integer dilation. Each original step
contributes a half-open segment, and the final vertex is included once.
Consequently common endpoints of consecutive segments are never duplicated.
-/

@[expose] public section

namespace GridHardness.LatticeSubdivision
set_option autoImplicit false

/-- The directed steps occurring consecutively in a route. -/
def edges : List Point → List (Point × Point)
  | [] => []
  | [_] => []
  | a :: b :: l => (a,b) :: edges (b :: l)

/-- Integer dilation followed by subdivision into unit steps. -/
def subdivide (s : Nat) : List Point → List Point
  | [] => []
  | [a] => [scale s a]
  | a :: b :: l => segmentInit s a b ++ subdivide s (b :: l)

theorem subdivide_length (s : Nat) (l : List Point) (hl : l ≠ []) :
    (subdivide s l).length=s*(l.length-1)+1 := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => simp [subdivide]
    | cons b l =>
      simp only [subdivide, List.length_append, segmentInit_length]
      rw [ih (by simp)]
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
      omega

theorem subdivide_ne_nil (s : Nat) (l : List Point) (hl : l ≠ []) :
    subdivide s l≠[] := by
  have h := subdivide_length s l hl
  intro he
  rw [he] at h
  simp at h

theorem subdivide_getLast (s : Nat) (l : List Point) :
    (subdivide s l).getLast?=l.getLast?.map (scale s) := by
  induction l with
  | nil => simp [subdivide]
  | cons a l ih =>
    cases l with
    | nil => simp [subdivide]
    | cons b l =>
      rw [subdivide, List.getLast?_append_of_ne_nil _
        (subdivide_ne_nil s (b::l) (by simp)), ih]
      simp

theorem subdivide_head (s : Nat) (hs : 0 < s) (l : List Point) :
    (subdivide s l).head?=l.head?.map (scale s) := by
  cases l with
  | nil => simp [subdivide]
  | cons a l =>
    cases l with
    | nil => simp [subdivide]
    | cons b l =>
      rw [subdivide, List.head?_append_of_ne_nil]
      · simpa using segmentInit_head hs a b
      · intro h
        have hh := segmentInit_length s a b
        rw [h] at hh
        simp at hh
        omega

theorem subdivide_chain (s : Nat) (hs : 0 < s) (l : List Point)
    (hl : l.IsChain UnitStep) : (subdivide s l).IsChain UnitStep := by
  induction l with
  | nil => simp [subdivide]
  | cons a l ih =>
    cases l with
    | nil => simp [subdivide]
    | cons b l =>
      have hab := (List.isChain_cons_cons.mp hl).1
      have hseg := segment_chain s hab
      rw [segment_eq_init_append] at hseg
      obtain ⟨hp,_,hbound⟩ := List.isChain_append.mp hseg
      rw [subdivide]
      apply hp.append (ih hl.tail)
      intro q hq r hr
      rw [subdivide_head s hs] at hr
      simp only [List.head?_cons,Option.map_some,Option.mem_some_iff] at hr
      subst r
      exact hbound q hq (scale s b) (by simp)

/-- Exact membership: a point is the scaled last vertex, or belongs to
the half-open subdivision of one of the original consecutive steps. -/
theorem subdivide_mem (s : Nat) (l : List Point) (q : Point) :
    q∈subdivide s l ↔
      (∃ a, l.getLast?=some a ∧ scale s a=q) ∨
      ∃ a b, (a,b)∈edges l ∧ ∃ k, k<s ∧ interpolate s a b k=q := by
  induction l with
  | nil => simp [subdivide,edges]
  | cons a l ih =>
    cases l with
    | nil => simp [subdivide,edges,eq_comm]
    | cons b l =>
      simp only [subdivide, List.mem_append, mem_segmentInit, ih, edges, List.mem_cons]
      constructor
      · rintro (hp | ht)
        · exact Or.inr ⟨a,b,Or.inl rfl,hp⟩
        · rcases ht with ⟨c,hc,hcq⟩ | ⟨c,d,hcd,hk⟩
          · exact Or.inl ⟨c,by simpa using hc,hcq⟩
          · exact Or.inr ⟨c,d,Or.inr hcd,hk⟩
      · rintro (⟨c,hc,hcq⟩ | ⟨c,d,hcd,hk⟩)
        · exact Or.inr (Or.inl ⟨c,by simpa using hc,hcq⟩)
        · rcases hcd with hcd | hcd
          · cases hcd
            exact Or.inl hk
          · exact Or.inr (Or.inr ⟨c,d,hcd,hk⟩)

theorem edges_mem_vertices (l : List Point) (a b : Point)
    (h : (a, b) ∈ edges l) : a∈l ∧ b∈l := by
  induction l with
  | nil => simp [edges] at h
  | cons c l ih =>
    cases l with
    | nil => simp [edges] at h
    | cons d l =>
      simp only [edges,List.mem_cons] at h
      rcases h with h | h
      · cases h
        simp
      · obtain ⟨ha,hb⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb⟩

theorem edges_unit (l : List Point) (hl : l.IsChain UnitStep)
    (a b : Point) (h : (a, b) ∈ edges l) : UnitStep a b := by
  induction l with
  | nil => simp [edges] at h
  | cons c l ih =>
    cases l with
    | nil => simp [edges] at h
    | cons d l =>
      simp only [edges,List.mem_cons] at h
      rcases h with h | h
      · cases h
        exact (List.isChain_cons_cons.mp hl).1
      · exact ih hl.tail h

/-- Every original route vertex survives as its scaled copy. -/
theorem scale_mem_subdivide (s : Nat) (hs : 0 < s) (l : List Point)
    (v : Point) (hv : v ∈ l) : scale s v∈subdivide s l := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    cases l with
    | nil =>
      have hv : v=a := by simpa using hv
      simp [subdivide,hv]
    | cons b l =>
      rw [subdivide,List.mem_append]
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        apply Or.inl
        exact (mem_segmentInit s a b _).mpr ⟨0,hs,interpolate_zero s a b⟩
      · exact Or.inr (ih hv)

/-- The inclusive segment of every original step is contained in the
subdivided route, including the endpoint shared with the next segment. -/
theorem segment_subset_subdivide (s : Nat) (hs : 0 < s) (l : List Point)
    (a b : Point) (hab : (a, b) ∈ edges l) (q : Point)
    (hq : q ∈ segment s a b) : q∈subdivide s l := by
  obtain ⟨k,hk,hq⟩ := (mem_segment s a b q).mp hq
  by_cases hks : k<s
  · exact (subdivide_mem s l q).mpr (Or.inr ⟨a,b,hab,k,hks,hq⟩)
  · have hks : k=s := by omega
    subst k
    rw [interpolate_scale] at hq
    rw [← hq]
    exact scale_mem_subdivide s hs l b (edges_mem_vertices l a b hab).2

theorem subdivide_length_le (s : Nat) (hs : 0 < s) (l : List Point) :
    (subdivide s l).length≤s*l.length := by
  cases l with
  | nil => simp [subdivide]
  | cons a l =>
    rw [subdivide_length s (a::l) (by simp)]
    simp only [List.length_cons,Nat.add_sub_cancel,Nat.mul_add,Nat.mul_one]
    omega

/-- Subdivision introduces no additional copies of original lattice vertices. -/
theorem scale_mem_subdivide_iff (s : Nat) (hs : 0 < s) (l : List Point)
    (hl : l.IsChain UnitStep) (v : Point) :
    scale s v∈subdivide s l ↔ v∈l := by
  constructor
  · intro hv
    rcases (subdivide_mem s l _).mp hv with ⟨a,ha,hav⟩ | ⟨a,b,hab,k,hk,he⟩
    · have hav : a=v := by
        apply Prod.ext
        · have h := congrArg Prod.fst hav
          dsimp [scale] at h
          nlinarith
        · have h := congrArg Prod.snd hav
          dsimp [scale] at h
          nlinarith
      subst a
      exact List.mem_of_mem_getLast? (by rw [ha]; simp)
    · have hav := interpolate_eq_scale_source s (edges_unit l hl a b hab) hk he
      subst a
      exact (edges_mem_vertices l v b hab).1
  · exact scale_mem_subdivide s hs l v

/-- Simplicity is preserved by integer subdivision. -/
theorem subdivide_nodup (s : Nat) (l : List Point)
    (hn : l.Nodup) (hl : l.IsChain UnitStep) : (subdivide s l).Nodup := by
  induction l with
  | nil => simp [subdivide]
  | cons a l ih =>
    cases l with
    | nil => simp [subdivide]
    | cons b l =>
      have hab := (List.isChain_cons_cons.mp hl).1
      obtain ⟨han,htn⟩ := List.nodup_cons.mp hn
      rw [subdivide,List.nodup_append]
      refine ⟨segmentInit_nodup s hab,ih htn hl.tail,?_⟩
      intro q hq r hr hqr
      obtain ⟨k,hk,hkq⟩ := (mem_segmentInit s a b q).mp hq
      rcases (subdivide_mem s (b::l) r).mp hr with ⟨c,hc,hcr⟩ | ⟨c,d,hcd,m,hm,hmr⟩
      · have hac := interpolate_eq_scale_source s hab hk (hkq.trans (hqr.trans hcr.symm))
        apply han
        rw [hac]
        exact List.mem_of_mem_getLast? (by rw [hc]; simp)
      · have had := interpolate_eq_source_endpoint s hab (edges_unit _ hl.tail c d hcd)
          hk (Nat.le_of_lt hm) (hkq.trans (hqr.trans hmr.symm))
        obtain ⟨hc,hd⟩ := edges_mem_vertices (b::l) c d hcd
        rcases had with rfl | rfl
        · exact han hc
        · exact han hd

/-- The first scaled edge is indexed directly from the source. -/
theorem subdivide_getElem_initial (s : Nat) (l : List Point) (hl : 2 ≤ l.length)
    (k : Nat) (hk : k < s) :
    (subdivide s l)[k]'(by
      rw [subdivide_length s l (by intro h; simp [h] at hl)]
      have hlen : 1≤l.length-1 := by omega
      have hm := Nat.mul_le_mul_left s hlen
      omega) = interpolate s (l[0]'(by omega)) (l[1]'(by omega)) k := by
  cases l with
  | nil => simp at hl
  | cons a l =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      simp only [subdivide]
      rw [List.getElem_append_left (by simpa using hk)]
      simp [segmentInit]

/-- The final scaled edge is indexed backwards from the target. -/
theorem subdivide_getElem_terminal (s : Nat) (_hs : 0 < s) (l : List Point)
    (hl : 2 ≤ l.length) (k : Nat) (hk : k < s) :
    (subdivide s l)[(subdivide s l).length-1-k]'(by
      have hlen := subdivide_length s l (by intro h; simp [h] at hl)
      omega) =
      interpolate s (l[l.length-1]'(by omega)) (l[l.length-2]'(by omega)) k := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      cases l with
      | nil =>
        have he : subdivide s [a,b]=segment s a b := by simp [subdivide]
        simp only [List.length_cons,List.length_nil] at *
        simp only [he,segment_length]
        have hle : k≤s := by omega
        simp only [segment,List.getElem_map,List.getElem_range,Nat.add_sub_cancel]
        change interpolate s a b (s-k)=interpolate s b a k
        rw [interpolate_reverse s a b (t:=s-k) (by omega)]
        congr 1
        omega
      | cons c l =>
        have htail := subdivide_length s (b::c::l) (by simp)
        have hbig : s+1≤(subdivide s (b::c::l)).length := by
          simp only [List.length_cons,Nat.add_sub_cancel] at htail
          have hm := Nat.mul_le_mul_left s (show 1≤l.length+1 by omega)
          omega
        change (segmentInit s a b ++ subdivide s (b::c::l))[(segmentInit s a b ++ subdivide s (b::c::l)).length-1-k]' (by simp only [List.length_append,segmentInit_length]; omega) = _
        rw [List.getElem_append_right]
        · have hi := ih (by simp)
          simp only [List.length_append,segmentInit_length]
          have hindex : s+(subdivide s (b::c::l)).length-1-k-s =
              (subdivide s (b::c::l)).length-1-k := by omega
          simp only [hindex]
          simpa using hi
        · simp only [List.length_append,segmentInit_length]
          omega

end GridHardness.LatticeSubdivision
