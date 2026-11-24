/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarMatched
public import GridHardness.SignedTentacleGraft

/-!
# Terminal Collar Matched Extension

Attach any of the eight recipient collars to an earlier signed
tentacle. The old drawing replaces the template's initial straight strip.
Its terminal rung must therefore reach that strip's far end, not merely
its outer radius-sixteen end. A finite local clearance test suffices for
validity and exact singleton docking, regardless of earlier bends.
-/

@[expose] public section

namespace GridHardness.TerminalCollarMatched
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 8192

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

def incoming (s : Fin 4) (b : Bool) : Finset Point := (phaseDrawing s b).basePoints
def tail (s : Fin 4) (b : Bool) : Finset Point := (phaseDrawing s b).tailPoints

/-- The new strips together with the target cluster are the complete
finite region against which prior-chain clearance is checked. -/
def guard (s : Fin 4) (b : Bool) : Finset Point :=
  tail s b ∪ TwoClusterAssembly.cluster TerminalCollar.clusterFrame

/-- Every old point either lies in the template's incoming strip or
stays at least two lattice steps from the new strips and target cluster. -/
def LocalClear (old : Drawing) (s : Fin 4) (b : Bool) : Prop :=
  ∀ p ∈ old.points, p∈incoming s b ∨
    ∀ q ∈ guard s b, 2 ≤ IntegerGrid.manhattan p q

instance (old : Drawing) (s : Fin 4) (b : Bool) : Decidable (LocalClear old s b) := by
  unfold LocalClear
  infer_instance

theorem base_tail_overlap : ∀ (s : Fin 4) (b : Bool),
    incoming s b ∩ tail s b =
      {(phaseDrawing s b).baseTip 0,(phaseDrawing s b).baseTip 1} := by decide +kernel

theorem incoming_cluster_apart : ∀ (s : Fin 4) (b : Bool),
    ClusterStar.Apart (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (incoming s b) := by decide +kernel

/-- The far rung of the incoming strip is the joining rung of the
first bend. The four sides have different inner radial coordinates. -/
theorem baseTip_coordinates (s : Fin 4) (b : Bool) (r : Fin 2) :
    (phaseDrawing s b).baseTip r =
      let δ : Int := if b then 1 else 0
      ![(-8,(r.val : Int)-δ),(δ-(r.val : Int),-9),
        (10,δ-(r.val : Int)),((r.val : Int)-δ,9)] s := by
  fin_cases s <;> cases b <;> fin_cases r <;> rfl

theorem tailSize (s : Fin 4) (b : Bool) :
    (phaseDrawing s b).tailSize = ![15,16,15,16] s + if b then 1 else 0 := by
  fin_cases s <;> cases b <;> rfl

theorem tail_bounds : ∀ (s : Fin 4) (b : Bool), ∀ p ∈ tail s b,
    -10 ≤ p.1 ∧ p.1 ≤ 10 ∧ -10 ≤ p.2 ∧ p.2 ≤ 10 := by decide +kernel

theorem tail_radius : ∀ (s : Fin 4) (b : Bool), ∀ p ∈ tail s b,
    IntegerGrid.manhattan (0,0) p ≤ 14 := by decide +kernel

theorem guard_bounds : ∀ (s : Fin 4) (b : Bool), ∀ p ∈ guard s b,
    -10 ≤ p.1 ∧ p.1 ≤ 10 ∧ -10 ≤ p.2 ∧ p.2 ≤ 10 := by decide +kernel

/-- Clearance concerns only a fixed finite neighborhood. This stronger
box test is one sufficient way of establishing the local condition. -/
theorem localClear_of_box (old : Drawing) (s : Fin 4) (b : Bool)
    (h : ∀ p ∈ old.points,
      -11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11 → p ∈ incoming s b) :
    LocalClear old s b := by
  intro p hp
  by_cases hi : p∈incoming s b
  · exact Or.inl hi
  · right
    intro q hq
    have hb := guard_bounds s b q hq
    have hn : ¬(-11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11) :=
      fun he => hi (h p hp he)
    dsimp [IntegerGrid.manhattan]
    omega

/-- The tip alignment supplies both old vertices on the joining rung;
local clearance excludes all other old contact with the new strips. -/
theorem graftClear_of_localClear (old : Drawing) (s : Fin 4) (b : Bool)
    (ho : old.Valid) (ht : Aligned old.tip (phaseDrawing s b).baseTip)
    (hc : LocalClear old s b) : Drawing.GraftClear old (phaseDrawing s b) := by
  constructor
  · intro p hp
    constructor
    · intro hpo
      rcases hc p hpo with hi | hfar
      · exact hi
      · have hh := hfar p (Finset.mem_union_left _ hp)
        simp [IntegerGrid.manhattan] at hh
    · intro hi
      have hm : p∈incoming s b ∩ tail s b := Finset.mem_inter.mpr ⟨hi,hp⟩
      rw [base_tail_overlap,Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · obtain ⟨r,hr⟩ := ht.range 0
        rw [hm,← hr]
        exact old.tip_mem ho r
      · obtain ⟨r,hr⟩ := ht.range 1
        rw [hm,← hr]
        exact old.tip_mem ho r
  · intro p hp q hq ha
    rcases hc p hp with hi | hfar
    · exact hi
    · have hh := hfar q (Finset.mem_union_left _ hq)
      change IntegerGrid.manhattan p q = 1 at ha
      omega

theorem prior_cluster_apart (old : Drawing) (s : Fin 4) (b : Bool)
    (hc : LocalClear old s b) :
    ClusterStar.Apart (TwoClusterAssembly.cluster TerminalCollar.clusterFrame) old.points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases hc p hq with hi | hfar
    · exact Finset.disjoint_left.mp (incoming_cluster_apart s b).1 hp hi
    · have hh := hfar p (Finset.mem_union_right _ hp)
      simp [IntegerGrid.manhattan] at hh
  · intro c hc' p hp ha
    rcases hc p hp with hi | hfar
    · exact (incoming_cluster_apart s b).2 c hc' p hi ha
    · have hh := hfar c (Finset.mem_union_right _ hc')
      have ha' := ha.symm
      change IntegerGrid.manhattan p c = 1 at ha'
      omega

/-- Replace just the initial strip, retaining all four certified bends. -/
def attach (old : Drawing) (s : Fin 4) (b : Bool) : Drawing :=
  Drawing.graft old (phaseDrawing s b)

theorem attach_valid (old : Drawing) (s : Fin 4) (b : Bool)
    (ho : old.Valid) (ht : Aligned old.tip (phaseDrawing s b).baseTip)
    (hc : LocalClear old s b) : (attach old s b).Valid :=
  Drawing.graft_valid old _ ho (phase_valid s b) ht (graftClear_of_localClear old s b ho ht hc)

theorem attach_start (old : Drawing) (s : Fin 4) (b : Bool) (r : Fin 2) :
    (attach old s b).start r=old.start r := Drawing.graft_start old _ r

theorem attach_tip (old : Drawing) (s : Fin 4) (b : Bool) (r : Fin 2) :
    (attach old s b).tip r=(phaseDrawing s b).tip r := by
  fin_cases s <;> cases b <;> rfl

theorem attach_points (old : Drawing) (s : Fin 4) (b : Bool) :
    (attach old s b).points=old.points ∪ tail s b := Drawing.graft_points old _

theorem attach_new_bounds (old : Drawing) (s : Fin 4) (b : Bool) {p : Point}
    (hp : p ∈ (attach old s b).points) (ho : p ∉ old.points) :
    -10 ≤ p.1 ∧ p.1 ≤ 10 ∧ -10 ≤ p.2 ∧ p.2 ≤ 10 := by
  rw [attach_points,Finset.mem_union] at hp
  exact tail_bounds s b p (hp.resolve_left ho)

theorem attach_card (old : Drawing) (s : Fin 4) (b : Bool)
    (ho : old.Valid) (ht : Aligned old.tip (phaseDrawing s b).baseTip)
    (hc : LocalClear old s b) :
    (attach old s b).points.card=old.points.card+
      2*(![15,16,15,16] s + if b then 1 else 0) := by
  change (Drawing.graft old (phaseDrawing s b)).points.card=_
  rw [Drawing.graft_card old _ ho (phase_valid s b) ht
    (graftClear_of_localClear old s b ho ht hc),tailSize]

theorem attach_card_le (old : Drawing) (s : Fin 4) (b : Bool)
    (ho : old.Valid) (ht : Aligned old.tip (phaseDrawing s b).baseTip)
    (hc : LocalClear old s b) :
    (attach old s b).points.card≤old.points.card+34 := by
  rw [attach_card old s b ho ht hc]
  fin_cases s <;> cases b <;> simp

theorem attach_cluster_disjoint (old : Drawing) (s : Fin 4) (b : Bool)
    (hc : LocalClear old s b) :
    Disjoint (TwoClusterAssembly.cluster TerminalCollar.clusterFrame) (attach old s b).points := by
  rw [attach_points]
  apply Finset.disjoint_union_right.mpr
  refine ⟨(prior_cluster_apart old s b hc).1,?_⟩
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (phase_cluster_disjoint s b) hp
    ((phaseDrawing s b).tail_subset hq)

/-- The earlier drawing creates no extra cluster edges; the retained
four bends contribute exactly the specified singleton recipient edge. -/
theorem attach_boundary (old : Drawing) (s : Fin 4) (b : Bool)
    (ho : old.Valid) (ht : Aligned old.tip (phaseDrawing s b).baseTip)
    (hc : LocalClear old s b) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (attach old s b).points =
        {(TwoClusterAssembly.corner TerminalCollar.clusterFrame s,(attach old s b).tip 0)} := by
  apply TwoClusterAssembly.boundary_eq_singleton
    (TwoClusterAssembly.corner_mem TerminalCollar.clusterFrame s)
    ((attach old s b).tip_mem (attach_valid old s b ho ht hc) 0)
  intro c hcc p hpp
  constructor
  · intro ha
    rw [attach_points,Finset.mem_union] at hpp
    rcases hpp with hpp | hpp
    · exact False.elim ((prior_cluster_apart old s b hc).2 c hcc p hpp ha)
    · have hm : (c,p)∈TwoClusterAssembly.boundary
          (TwoClusterAssembly.cluster TerminalCollar.clusterFrame) (phaseDrawing s b).points :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨hcc,(phaseDrawing s b).tail_subset hpp⟩,ha⟩
      rw [phase_boundary_singleton,Finset.mem_singleton,Prod.mk.injEq] at hm
      rwa [attach_tip]
  · rintro ⟨rfl,rfl⟩
    rw [attach_tip]
    have hm : (TwoClusterAssembly.corner TerminalCollar.clusterFrame s,(phaseDrawing s b).tip 0)∈
        TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
          (phaseDrawing s b).points := by rw [phase_boundary_singleton]; simp
    exact (Finset.mem_filter.mp hm).2

end GridHardness.TerminalCollarMatched
