/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollar

/-!
# Terminal Collar Extension

Attach the terminal detour to an arbitrary earlier signed tentacle.
Only a bounded neighborhood of the new collar is required to be clear;
the previous drawing may otherwise bend and travel arbitrarily.
-/

@[expose] public section

namespace GridHardness.TerminalCollar
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def firstAfter (d : Drawing) : Drawing := .attach d northFrame 3
def secondAfter (d : Drawing) : Drawing := .attach (firstAfter d) upperFrame 3
def thirdAfter (d : Drawing) : Drawing := .attach (secondAfter d) southFrame 5
def append (d : Drawing) : Drawing := .attach (thirdAfter d) terminalFrame 4

/-- Inside a one-step neighborhood of the collar and target cluster, the previous drawing
occupies only the two incoming lanes on the left of the joining rung. -/
def Frontier (d : Drawing) : Prop := ∀ p ∈ d.points,
  -9 ≤ p.1 ∧ p.1 ≤ 3 ∧ -3 ≤ p.2 ∧ p.2 ≤ 5 →
    p.1 ≤ -8 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

theorem incoming_frontier (n : Nat) : Frontier (.base (incomingFrame n) n) := by
  intro p hp _
  exact (mem_incoming n p).mp hp |>.2

theorem frontier_at_collar {d : Drawing} (h : Frontier d) {p : Point}
    (hp : p ∈ d.points) (hq : p ∈ collarPoints) :
    p.1 ≤ -8 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  have hb := collar_bounds hq
  exact h p hp (by omega)

theorem frontier_near_collar {d : Drawing} (h : Frontier d) {p q : Point}
    (hp : p ∈ d.points) (hq : q ∈ collarPoints) (ha : lattice.Adj p q) :
    p.1 ≤ -8 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  have hb := collar_bounds hq
  apply h p hp
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hb ⊢
  omega

theorem north_subset_collar : strip northFrame 3 ⊆ collarPoints := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))

theorem upper_subset_collar : strip upperFrame 3 ⊆ collarPoints := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hp))

theorem south_subset_collar : strip southFrame 5 ⊆ collarPoints := by
  intro p hp
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hp)

theorem terminal_subset_collar : strip terminalFrame 4 ⊆ collarPoints := by
  intro p hp
  exact Finset.mem_union_right _ hp

/-- Either ordering of the incoming terminal lanes is accepted. -/
theorem aligned_rung_mem (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (r : Fin 2) :
    (-8,(r.val : Int)) ∈ d.points := by
  obtain ⟨t,he⟩ := ht.range r
  rw [← he]
  exact d.tip_mem hv t

theorem firstAfter_overlap (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    d.points ∩ strip northFrame 3 = {join northFrame 0, join northFrame 1} := by
  have h0 : (-8,0) ∈ d.points := by simpa using aligned_rung_mem d hv ht 0
  have h1 : (-8,1) ∈ d.points := by simpa using aligned_rung_mem d hv ht 1
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hp
    have hx := frontier_at_collar hf hp (north_subset_collar hq)
    have hy := (mem_north p).mp hq
    rcases p with ⟨x,y⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, join, northFrame,
      Frame.map, place, sign, Bool.false_eq_true, ite_false, Fin.val_zero,
      Fin.val_one, Int.natCast_zero, Int.natCast_one, add_zero, Prod.mk.injEq]
    dsimp at hx hy
    omega
  · intro hp
    have he : p = (-8,0) ∨ p = (-8,1) := by simpa [join, northFrame,
      Frame.map, place, sign] using hp
    rcases he with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨h0,(mem_north _).mpr (by decide)⟩
    · exact Finset.mem_inter.mpr ⟨h1,(mem_north _).mpr (by decide)⟩

theorem firstAfter_separated (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    Separated d.points (strip northFrame 3) := by
  have h0 : (-8,0) ∈ d.points := by simpa using aligned_rung_mem d hv ht 0
  have h1 : (-8,1) ∈ d.points := by simpa using aligned_rung_mem d hv ht 1
  intro p hp q hq ha
  have hx := frontier_near_collar hf hp (north_subset_collar hq) ha
  have hy := (mem_north q).mp hq
  by_cases hn : p ∈ strip northFrame 3
  · exact Or.inl hn
  · right
    have he : q = (-8,0) ∨ q = (-8,1) := by
      rw [mem_north] at hn
      change IntegerGrid.manhattan p q = 1 at ha
      rw [manhattan_one_iff] at ha
      rcases p with ⟨x,y⟩
      rcases q with ⟨u,v⟩
      simp only [Prod.mk.injEq] at ha ⊢
      dsimp at hx hy hn
      omega
    exact he.elim (fun he => he ▸ h0) (fun he => he ▸ h1)

theorem firstAfter_valid (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    (firstAfter d).Valid := by
  refine ⟨hv,by decide,?_,firstAfter_overlap d hv ht hf,firstAfter_separated d hv ht hf⟩
  have hj : join northFrame = (fun r : Fin 2 => (-8, (r.val : Int))) := by
    funext r
    simp [join,northFrame,Frame.map,place,sign]
  rw [hj]
  exact ht

/-- The three remaining strips are disjoint from, and nonadjacent to,
the entire earlier drawing. -/
theorem tail_clear (d : Drawing) (hf : Frontier d) {q : Point}
    (hq : q ∈ strip upperFrame 3 ∪ strip southFrame 5 ∪ strip terminalFrame 4) :
    q ∉ d.points ∧ ∀ p ∈ d.points, ¬lattice.Adj p q := by
  have hc : q ∈ collarPoints := by
    simp only [Finset.mem_union] at hq
    rcases hq with (hq | hq) | hq
    · exact upper_subset_collar hq
    · exact south_subset_collar hq
    · exact terminal_subset_collar hq
  have hb := hq
  simp only [Finset.mem_union,mem_upper,mem_south,mem_terminal] at hb
  constructor
  · intro hp
    have hh := frontier_at_collar hf hp hc
    omega
  · intro p hp ha
    have hh := frontier_near_collar hf hp hc ha
    change IntegerGrid.manhattan p q = 1 at ha
    rw [manhattan_one_iff] at ha
    rcases p with ⟨x,y⟩
    rcases q with ⟨u,v⟩
    simp only [Prod.mk.injEq] at ha
    dsimp at hb hh
    omega

theorem secondAfter_overlap (d : Drawing) (hf : Frontier d) :
    (firstAfter d).points ∩ strip upperFrame 3 = {join upperFrame 0, join upperFrame 1} := by
  ext p
  have he : p ∈ strip upperFrame 3 → p ∉ d.points := fun hp =>
    (tail_clear d hf (Finset.mem_union_left _ (Finset.mem_union_left _ hp))).1
  have hc := congrArg (fun S : Finset Point => p ∈ S) (second_overlap 0)
  have hn : p ∈ strip (incomingFrame 0) 0 → p ∈ strip northFrame 3 := by
    rw [mem_incoming,mem_north]
    omega
  simp only [firstAfter,first,Drawing.points,Finset.mem_inter,Finset.mem_union] at hc ⊢
  tauto

theorem secondAfter_separated (d : Drawing) (hf : Frontier d) :
    Separated (firstAfter d).points (strip upperFrame 3) := by
  intro p hp q hq ha
  rcases Finset.mem_union.mp hp with hp | hp
  · exact False.elim ((tail_clear d hf
      (Finset.mem_union_left _ (Finset.mem_union_left _ hq))).2 p hp ha)
  · have hh := second_separated 0 p (Finset.mem_union_right _ hp) q hq ha
    rcases hh with hh | hh
    · exact Or.inl hh
    · right
      rcases Finset.mem_union.mp hh with hh | hh
      · apply Finset.mem_union_right
        change q ∈ strip (incomingFrame 0) 0 at hh
        rw [mem_incoming] at hh
        rw [mem_north]
        omega
      · exact Finset.mem_union_right _ hh

theorem secondAfter_valid (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    (secondAfter d).Valid := by
  refine ⟨firstAfter_valid d hv ht hf,by decide,?_,secondAfter_overlap d hf,
    secondAfter_separated d hf⟩
  left
  constructor <;> rfl

theorem thirdAfter_overlap (d : Drawing) (hf : Frontier d) :
    (secondAfter d).points ∩ strip southFrame 5 = {join southFrame 0, join southFrame 1} := by
  ext p
  have he : p ∈ strip southFrame 5 → p ∉ d.points := fun hp =>
    (tail_clear d hf (Finset.mem_union_left _ (Finset.mem_union_right _ hp))).1
  have hc := congrArg (fun S : Finset Point => p ∈ S) (third_overlap 0)
  have hn : p ∈ strip (incomingFrame 0) 0 → p ∈ strip northFrame 3 := by
    rw [mem_incoming,mem_north]
    omega
  simp only [secondAfter,firstAfter,second,first,Drawing.points,
    Finset.mem_inter,Finset.mem_union] at hc ⊢
  tauto

theorem thirdAfter_separated (d : Drawing) (hf : Frontier d) :
    Separated (secondAfter d).points (strip southFrame 5) := by
  intro p hp q hq ha
  simp only [secondAfter,firstAfter,Drawing.points,Finset.mem_union] at hp
  rcases hp with (hp | hp) | hp
  · exact False.elim ((tail_clear d hf
      (Finset.mem_union_left _ (Finset.mem_union_right _ hq))).2 p hp ha)
  all_goals
    have hm : p ∈ (second 0).points := by
      simp only [second,first,Drawing.points,Finset.mem_union]
      tauto
    have hh := third_separated 0 p hm q hq ha
    rcases hh with hh | hh
    · exact Or.inl hh
    · right
      simp only [second,first,Drawing.points,Finset.mem_union] at hh
      simp only [secondAfter,firstAfter,Drawing.points,Finset.mem_union]
      have hn : q ∈ strip (incomingFrame 0) 0 → q ∈ strip northFrame 3 := by
        rw [mem_incoming,mem_north]
        omega
      tauto

theorem thirdAfter_valid (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    (thirdAfter d).Valid := by
  refine ⟨secondAfter_valid d hv ht hf,by decide,?_,thirdAfter_overlap d hf,
    thirdAfter_separated d hf⟩
  right
  constructor <;> rfl

theorem append_overlap (d : Drawing) (hf : Frontier d) :
    (thirdAfter d).points ∩ strip terminalFrame 4 = {join terminalFrame 0, join terminalFrame 1} := by
  ext p
  have he : p ∈ strip terminalFrame 4 → p ∉ d.points := fun hp =>
    (tail_clear d hf (Finset.mem_union_right _ hp)).1
  have hc := congrArg (fun S : Finset Point => p ∈ S) (terminal_overlap 0)
  have hn : p ∈ strip (incomingFrame 0) 0 → p ∈ strip northFrame 3 := by
    rw [mem_incoming,mem_north]
    omega
  simp only [thirdAfter,secondAfter,firstAfter,third,second,first,Drawing.points,
    Finset.mem_inter,Finset.mem_union] at hc ⊢
  tauto

theorem append_separated (d : Drawing) (hf : Frontier d) :
    Separated (thirdAfter d).points (strip terminalFrame 4) := by
  intro p hp q hq ha
  simp only [thirdAfter,secondAfter,firstAfter,Drawing.points,Finset.mem_union] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · exact False.elim ((tail_clear d hf (Finset.mem_union_right _ hq)).2 p hp ha)
  all_goals
    have hm : p ∈ (third 0).points := by
      simp only [third,second,first,Drawing.points,Finset.mem_union]
      tauto
    have hh := terminal_separated 0 p hm q hq ha
    rcases hh with hh | hh
    · exact Or.inl hh
    · right
      simp only [third,second,first,Drawing.points,Finset.mem_union] at hh
      simp only [thirdAfter,secondAfter,firstAfter,Drawing.points,Finset.mem_union]
      have hn : q ∈ strip (incomingFrame 0) 0 → q ∈ strip northFrame 3 := by
        rw [mem_incoming,mem_north]
        omega
      tauto

/-- A local clearance certificate suffices to append the fixed collar
to an arbitrary valid earlier tentacle. -/
theorem append_valid (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    (append d).Valid := by
  refine ⟨thirdAfter_valid d hv ht hf,by decide,?_,append_overlap d hf,
    append_separated d hf⟩
  left
  constructor <;> rfl

theorem append_start (d : Drawing) (r : Fin 2) : (append d).start r = d.start r := rfl

theorem append_tip (d : Drawing) (r : Fin 2) :
    (append d).tip r = (-1,-1-(r.val : Int)) := tip_coordinates 0 r

theorem append_points (d : Drawing) : (append d).points = d.points ∪ collarPoints := by
  simp only [append,thirdAfter,secondAfter,firstAfter,Drawing.points,
    collarPoints,Finset.union_assoc]

/-- Every new point lies in the same fixed eight-by-seven coordinate box. -/
theorem append_new_bounds (d : Drawing) {p : Point} (hp : p ∈ (append d).points)
    (ho : p ∉ d.points) : -8 ≤ p.1 ∧ p.1 ≤ -1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 4 := by
  rw [append_points,Finset.mem_union] at hp
  exact collar_bounds (hp.resolve_left ho)

theorem append_card (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    (append d).points.card = d.points.card + 30 := by
  rw [Drawing.card _ (append_valid d hv ht hf),Drawing.card _ hv]
  simp only [append,thirdAfter,secondAfter,firstAfter,Drawing.halfSize]
  omega

theorem frontier_cluster_clear (d : Drawing) (hf : Frontier d) :
    Disjoint (TwoClusterAssembly.cluster clusterFrame) d.points ∧
      ∀ c ∈ TwoClusterAssembly.cluster clusterFrame, ∀ p ∈ d.points, ¬lattice.Adj c p := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hb := (mem_cluster p).mp hp
    have hh := hf p hq (by omega)
    omega
  · intro c hc p hp ha
    have hb := (mem_cluster c).mp hc
    have hn : -9 ≤ p.1 ∧ p.1 ≤ 3 ∧ -3 ≤ p.2 ∧ p.2 ≤ 5 := by
      change IntegerGrid.manhattan c p = 1 at ha
      rw [manhattan_one_iff] at ha
      rcases c with ⟨x,y⟩
      rcases p with ⟨u,v⟩
      simp only [Prod.mk.injEq] at ha
      dsimp at hb ⊢
      omega
    have hh := hf p hp hn
    change IntegerGrid.manhattan c p = 1 at ha
    rw [manhattan_one_iff] at ha
    rcases c with ⟨x,y⟩
    rcases p with ⟨u,v⟩
    simp only [Prod.mk.injEq] at ha
    dsimp at hb hh
    omega

theorem append_cluster_disjoint (d : Drawing) (hf : Frontier d) :
    Disjoint (TwoClusterAssembly.cluster clusterFrame) (append d).points := by
  rw [append_points]
  apply Finset.disjoint_union_right.mpr
  refine ⟨(frontier_cluster_clear d hf).1,?_⟩
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (cluster_disjoint 0) hp (by
    rw [points_union]
    exact Finset.mem_union_right _ hq)

/-- Exact singleton docking is preserved for arbitrary preceding
tentacles satisfying the bounded clearance condition. -/
theorem append_cluster_boundary (d : Drawing) (hf : Frontier d) {c t : Point}
    (hc : c ∈ TwoClusterAssembly.cluster clusterFrame) (ht : t ∈ (append d).points) :
    lattice.Adj c t ↔ c = TwoClusterAssembly.corner clusterFrame 0 ∧ t = (append d).tip 0 := by
  constructor
  · intro ha
    rw [append_points,Finset.mem_union] at ht
    rcases ht with ht | ht
    · exact False.elim ((frontier_cluster_clear d hf).2 c hc t ht ha)
    · have hm : t ∈ (drawing 0).points := by
        rw [points_union]
        exact Finset.mem_union_right _ ht
      exact (cluster_boundary 0 hc hm).mp ha
  · rintro ⟨rfl,rfl⟩
    change IntegerGrid.manhattan _ _ = 1
    simp only [append,Drawing.tip,terminalFrame,SignedTentacle.far,
      TwoClusterAssembly.corner,clusterFrame,Frame.map,NineClusterAttachment.corner,
      NineCluster.point,NineCluster.port,place,sign]
    decide

theorem append_boundary_singleton (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8, (r.val : Int)))) (hf : Frontier d) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster clusterFrame) (append d).points =
      {(TwoClusterAssembly.corner clusterFrame 0, (append d).tip 0)} := by
  exact TwoClusterAssembly.boundary_eq_singleton
    (TwoClusterAssembly.corner_mem clusterFrame 0)
    ((append d).tip_mem (append_valid d hv ht hf) 0)
    (fun _ hc _ hm => append_cluster_boundary d hf hc hm)

end GridHardness.TerminalCollar
