/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.ClusterStar

/-!
# Grid Assembly Local

Concrete regional geometry for a global grid assembly. Odd-side bodies
are placed nine-clusters. Even-side bodies additionally own up to three signed
tentacles. All local routing is derived from coordinate/docking validity.
-/

@[expose] public section

namespace GridHardness.GridAssembly
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev Arm := Option (Fin 4 × Drawing)
abbrev Arms := Fin 3 → Arm

def armPoints : Arm → Finset Point
  | none => ∅
  | some (_, d) => d.points

def armHalfSize : Arm → Nat
  | none => 0
  | some (_, d) => d.halfSize

def Arm.Valid : Arm → Prop
  | none => True
  | some (side, d) => d.Valid ∧ NineClusterAttachment.Docked true side d

def Arm.Apart : Arm → Arm → Prop
  | some (side, d), some (side', e) => side ≠ side' ∧ ClusterStar.Apart d.points e.points
  | _, _ => True

def Arms.Valid (arms : Arms) : Prop :=
  (∀ i, (arms i).Valid) ∧ ∀ i j, i ≠ j → (arms i).Apart (arms j)

instance (a : Arm) : Decidable a.Valid := by cases a <;> unfold Arm.Valid <;> infer_instance
instance (a b : Arm) : Decidable (a.Apart b) := by
  cases a <;> cases b <;> unfold Arm.Apart <;> infer_instance
instance (arms : Arms) : Decidable arms.Valid := by unfold Arms.Valid; infer_instance

def Arms.points (arms : Arms) : Finset Point :=
  NineClusterAttachment.points ∪ Finset.univ.biUnion (fun i => armPoints (arms i))

def armPort (f : Frame) (a : Arm) (p : Point) : Prop :=
  match a with
  | none => False
  | some (_, d) => p = f.map (d.tip 0) ∧ color (d.tip 0) = 0

instance (f : Frame) (a : Arm) (p : Point) : Decidable (armPort f a p) := by
  cases a <;> unfold armPort <;> infer_instance

private theorem remaining (i j : Fin 3) (h : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | decide

theorem Arms.route (arms : Arms) (hv : arms.Valid) (f : Frame) (a b : Point)
    (ha : ∃ i, armPort f (arms i) a) (hb : ∃ j, armPort f (arms j) b) (hne : a ≠ b) :
    HasRoute (arms.points.image f.map) a b := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  cases hai : arms i with
  | none => simp [hai, armPort] at hi
  | some ai =>
    rcases ai with ⟨si, di⟩
    cases haj : arms j with
    | none => simp [haj, armPort] at hj
    | some aj =>
      rcases aj with ⟨sj, dj⟩
      have hi' : a = f.map (di.tip 0) ∧ color (di.tip 0) = 0 := by simpa [hai, armPort] using hi
      have hj' : b = f.map (dj.tip 0) ∧ color (dj.tip 0) = 0 := by simpa [haj, armPort] using hj
      have hij : i ≠ j := by
        intro he
        subst j
        have he := Option.some.inj (hai.symm.trans haj)
        have hd : di = dj := congrArg Prod.snd he
        exact hne (hi'.1.trans ((congrArg (fun d : Drawing => f.map (d.tip 0)) hd).trans hj'.1.symm))
      obtain ⟨k, hki, hkj, hall⟩ := remaining i j hij
      let s : ClusterStar.Star := ⟨di, dj, si, sj, arms k⟩
      have hdi : di.Valid ∧ NineClusterAttachment.Docked true si di := by
        simpa [hai, Arm.Valid] using hv.1 i
      have hdj : dj.Valid ∧ NineClusterAttachment.Docked true sj dj := by
        simpa [haj, Arm.Valid] using hv.1 j
      have hpair : si ≠ sj ∧ ClusterStar.Apart di.points dj.points := by
        simpa [hai, haj, Arm.Apart] using hv.2 i j hij
      have hs : s.Valid := by
        refine ⟨hdi.1, hdj.1, hdi.2, hdj.2, hpair.1, hpair.2, ?_⟩
        cases hak : arms k with
        | none => simp only [s, hak]
        | some ak =>
          rcases ak with ⟨sk, dk⟩
          have hdk : dk.Valid ∧ NineClusterAttachment.Docked true sk dk := by
            simpa [hak, Arm.Valid] using hv.1 k
          have hk_i : sk ≠ si ∧ ClusterStar.Apart dk.points di.points := by
            simpa [hak, hai, Arm.Apart] using hv.2 k i hki
          have hk_j : sk ≠ sj ∧ ClusterStar.Apart dk.points dj.points := by
            simpa [hak, haj, Arm.Apart] using hv.2 k j hkj
          simp only [s, hak]
          exact ⟨hdk.1, hdk.2, hk_i.1, hk_j.1, hk_i.2.symm, hk_j.2.symm⟩
      have hpoints : s.points = arms.points := by
        have hdi : di.points = armPoints (arms i) := by rw [hai]; rfl
        have hdj : dj.points = armPoints (arms j) := by rw [haj]; rfl
        change (NineClusterAttachment.points ∪ armPoints (arms k) ∪ di.points ∪ dj.points) = _
        rw [hdi, hdj]
        ext p
        simp only [Arms.points, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro (((hp | hp) | hp) | hp)
          · exact Or.inl hp
          · exact Or.inr ⟨k, hp⟩
          · exact Or.inr ⟨i, hp⟩
          · exact Or.inr ⟨j, hp⟩
        · rintro (hp | ⟨l, hp⟩)
          · exact Or.inl (Or.inl (Or.inl hp))
          · rcases hall l with rfl | rfl | rfl
            · exact Or.inl (Or.inr hp)
            · exact Or.inr hp
            · exact Or.inl (Or.inl (Or.inr hp))
      have hr := f.route (s.route hs 0 0 hi'.2 hj'.2)
      simpa only [hpoints, hi'.1, hj'.1] using hr

/-- Two concrete kinds of placed regional body. -/
inductive Body where
  | cluster (frame : Frame)
  | star (frame : Frame) (arms : Arms)

def Body.frame : Body → Frame | .cluster f => f | .star f _ => f

def Body.ownsTentacles : Body → Bool | .cluster _ => false | .star _ _ => true

def Body.Valid : Body → Prop | .cluster _ => True | .star _ arms => arms.Valid

def Body.points : Body → Finset Point
  | .cluster f => NineClusterAttachment.points.image f.map
  | .star f arms => arms.points.image f.map

def Body.halfTentacleSize : Body → Nat
  | .cluster _ => 0
  | .star _ arms => ∑ i : Fin 3, armHalfSize (arms i)

def Body.IsPort : Body → Point → Prop
  | .cluster f, p => ∃ i : Fin 4, p = f.map (NineClusterAttachment.corner i)
  | .star f arms, p => ∃ i : Fin 3, armPort f (arms i) p

instance (b : Body) : Decidable b.Valid := by cases b <;> unfold Body.Valid <;> infer_instance
instance (b : Body) (p : Point) : Decidable (b.IsPort p) := by
  cases b <;> unfold Body.IsPort <;> infer_instance

/-- Universal local route, derived from the specified geometric body. -/
theorem Body.route (body : Body) (hv : body.Valid) (a b : Point)
    (ha : body.IsPort a) (hb : body.IsPort b) (hne : a ≠ b) : HasRoute body.points a b := by
  cases body with
  | cluster f =>
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact TwoClusterAssembly.cluster_route f i j (fun he => hne (he ▸ rfl))
  | star f arms => exact arms.route hv f a b ha hb hne

def Body.anchor (body : Body) : Point := body.frame.map (NineClusterAttachment.corner 0)

theorem Body.anchor_mem (body : Body) : body.anchor ∈ body.points := by
  cases body with
  | cluster f => exact Finset.mem_image.mpr ⟨_, NineClusterAttachment.corner_mem 0, rfl⟩
  | star f arms =>
    exact Finset.mem_image.mpr ⟨_, Finset.mem_union_left _ (NineClusterAttachment.corner_mem 0), rfl⟩

theorem Body.port_mem (body : Body) (hv : body.Valid) (p : Point) (hp : body.IsPort p) :
    p ∈ body.points := by
  cases body with
  | cluster f =>
    obtain ⟨i, rfl⟩ := hp
    exact Finset.mem_image.mpr ⟨_, NineClusterAttachment.corner_mem i, rfl⟩
  | star f arms =>
    obtain ⟨i, hi⟩ := hp
    cases he : arms i with
    | none => simp [he, armPort] at hi
    | some arm =>
      rcases arm with ⟨side, d⟩
      have hi' : p = f.map (d.tip 0) ∧ color (d.tip 0) = 0 := by simpa [he, armPort] using hi
      have hd : d.Valid ∧ NineClusterAttachment.Docked true side d := by
        simpa [he, Arm.Valid] using hv.1 i
      rw [hi'.1]
      apply Finset.mem_image.mpr
      refine ⟨_, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩), rfl⟩
      simpa [he, armPoints] using d.tip_mem hd.1 0

theorem Arm.points_card (a : Arm) (hv : a.Valid) :
    (armPoints a).card = 2 * armHalfSize a := by
  cases a with
  | none => simp [armPoints, armHalfSize]
  | some arm => exact arm.2.card hv.1

theorem Arm.cluster_disjoint (a : Arm) (hv : a.Valid) :
    Disjoint NineClusterAttachment.points (armPoints a) := by
  cases a with
  | none => simp [armPoints]
  | some arm => exact hv.2.disjoint

theorem Arm.disjoint (a b : Arm) (h : a.Apart b) :
    Disjoint (armPoints a) (armPoints b) := by
  cases a <;> cases b
  · simp [armPoints]
  · simp [armPoints]
  · simp [armPoints]
  · exact h.2.1

theorem Arms.points_card (arms : Arms) (hv : arms.Valid) :
    arms.points.card = 9 + 2 * ∑ i : Fin 3, armHalfSize (arms i) := by
  have hc : NineClusterAttachment.points.card = 9 := by
    unfold NineClusterAttachment.points
    rw [Finset.card_image_of_injective _ NineCluster.point_injective]
    simp
  have hdis : Disjoint NineClusterAttachment.points
      (Finset.univ.biUnion (fun i => armPoints (arms i))) := by
    apply (Finset.disjoint_biUnion_right _ _ _).mpr
    intro i _
    exact (arms i).cluster_disjoint (hv.1 i)
  have hp : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun i => armPoints (arms i)) := by
    intro i _ j _ hij
    exact (arms i).disjoint (arms j) (hv.2 i j hij)
  rw [Arms.points, Finset.card_union_of_disjoint hdis, hc, Finset.card_biUnion hp]
  simp only [Arm.points_card _ (hv.1 _), Finset.mul_sum]

theorem Body.points_card (body : Body) (hv : body.Valid) :
    body.points.card = 9 + 2 * body.halfTentacleSize := by
  cases body with
  | cluster f =>
    change (NineClusterAttachment.points.image f.map).card = 9 + 2*0
    rw [Finset.card_image_of_injective _ f.injective]
    unfold NineClusterAttachment.points
    rw [Finset.card_image_of_injective _ NineCluster.point_injective]
    simp
  | star f arms =>
    change (arms.points.image f.map).card = _
    rw [Finset.card_image_of_injective _ f.injective, arms.points_card hv]
    rfl

end GridHardness.GridAssembly
