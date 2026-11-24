/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteTentacleSeparation

/-!
# SAT Complete Regions

The actual finite regions: every cluster owns exactly its outgoing
complete tentacles. Pairwise separation and all inter-region contacts are
proved directly from the concrete geometric construction.
-/

@[expose] public section

namespace GridHardness.SatCompleteRegions
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open SatCompleteTentacles
set_option autoImplicit false
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true

local instance regionsAdjDecidable : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q=1))

noncomputable def region (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) : Finset Point := by
  classical
  letI := Fintype.ofFinite (Edge x)
  exact SatNineClusterPlacement.points x hw v ∪
    Finset.univ.biUnion (fun e : Edge x => if SatDockCorridors.owner x e=v then (drawing x hw e).points else ∅)

theorem mem_region (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) (p : Point) :
    p∈region x hw v ↔ p∈SatNineClusterPlacement.points x hw v ∨
      ∃ e : Edge x, SatDockCorridors.owner x e=v ∧ p∈(drawing x hw e).points := by
  classical
  simp only [region, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply or_congr Iff.rfl
  apply exists_congr
  intro e
  split_ifs <;> simp_all

theorem cluster_subset (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    SatNineClusterPlacement.points x hw v ⊆ region x hw v :=
  fun p hp => (mem_region x hw v p).mpr (Or.inl hp)

theorem drawing_subset (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).points ⊆ region x hw (SatDockCorridors.owner x e) :=
  fun p hp => (mem_region x hw _ p).mpr (Or.inr ⟨e,rfl,hp⟩)

/-- Even the two incident clusters are disjoint from a complete tentacle. -/
theorem cluster_drawing_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) :
    Disjoint (SatNineClusterPlacement.points x hw v) (drawing x hw e).points := by
  by_cases ho : v=SatDockCorridors.owner x e
  · subst v; exact owner_disjoint x hw e
  by_cases hr : v=SatDockCorridors.recipient x e
  · subst v; exact recipient_disjoint x hw e
  exact (unrelated_cluster_apart x hw e v ho hr).1

/-- Assigning each tentacle to its owner gives genuinely disjoint regions. -/
theorem disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) : Disjoint (region x hw v) (region x hw w) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rw [mem_region] at hp hq
  rcases hp with hp|⟨e,he,hp⟩ <;> rcases hq with hq|⟨f,hf,hq⟩
  · exact Finset.disjoint_left.mp (SatNineClusterPlacement.points_disjoint x hw v w hvw) hp hq
  · exact Finset.disjoint_left.mp (cluster_drawing_disjoint x hw v f) hp hq
  · exact Finset.disjoint_left.mp (cluster_drawing_disjoint x hw w e) hq hp
  · have hef : e≠f := fun h => hvw (he.symm.trans ((congrArg (SatDockCorridors.owner x) h).trans hf))
    exact Finset.disjoint_left.mp (pairwise_apart x hw e f hef).1 hp hq

private theorem boundary_endpoints (S T : Finset Point) (p q a b : Point)
    (h : TwoClusterAssembly.boundary S T = {(a, b)})
    (hp : p ∈ S) (hq : q ∈ T) (ha : lattice.Adj p q) : p = a ∧ q = b := by
  have hm := (TwoClusterAssembly.mem_boundary S T p q).mpr ⟨hp, hq, ha⟩
  rw [h] at hm
  have he : (p, q) = (a, b) := Finset.mem_singleton.mp hm
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

-- This naming linter unfolds the full source-dependent vertex type.
set_option linter.constructorNameAsVariable false in
/-- A cluster outside the owning region can meet a tentacle only at its
recipient, through the proved singleton boundary. -/
theorem cluster_drawing_adj_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) (hv : v ≠SatDockCorridors.owner x e)
    (p q : Point) (hp : p ∈SatNineClusterPlacement.points x hw v)
    (hq : q ∈(drawing x hw e).points) :
    lattice.Adj p q ↔ v=SatDockCorridors.recipient x e ∧
      p=SatNineClusterPlacement.corner x hw v (side x hw e) ∧ q=(drawing x hw e).tip 0 := by
  by_cases hr : v=SatDockCorridors.recipient x e
  · subst v
    constructor
    · intro ha
      have he := boundary_endpoints
        (SatNineClusterPlacement.points x hw (SatDockCorridors.recipient x e))
        (drawing x hw e).points p q
        (SatNineClusterPlacement.corner x hw (SatDockCorridors.recipient x e) (side x hw e))
        ((drawing x hw e).tip 0) (recipient_boundary x hw e) hp hq ha
      exact ⟨rfl, he⟩
    · rintro ⟨_,rfl,rfl⟩
      exact (between x hw e).tip_adjacent.symm
  · constructor
    · intro ha
      exact False.elim ((unrelated_cluster_apart x hw e v hv hr).2 p hp q hq ha)
    · exact fun h => False.elim (hr h.1)

/-- The only edges between distinct regions are the designated terminal
edges of the complete tentacles connecting those graph vertices. -/
theorem adjacent_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) (p q : Point)
    (hp : p ∈region x hw v) (hq : q ∈region x hw w) :
    lattice.Adj p q ↔
      (∃ e : Edge x, SatDockCorridors.owner x e=v ∧ SatDockCorridors.recipient x e=w ∧
        p=(drawing x hw e).tip 0 ∧ q=SatNineClusterPlacement.corner x hw w (side x hw e)) ∨
      (∃ e : Edge x, SatDockCorridors.owner x e=w ∧ SatDockCorridors.recipient x e=v ∧
        q=(drawing x hw e).tip 0 ∧ p=SatNineClusterPlacement.corner x hw v (side x hw e)) := by
  constructor
  · intro ha
    rw [mem_region] at hp hq
    rcases hp with hp|⟨e,he,hp⟩ <;> rcases hq with hq|⟨f,hf,hq⟩
    · exact False.elim (SatNineClusterPlacement.points_nonadjacent x hw v w hvw p q hp hq ha)
    · have hv : v≠SatDockCorridors.owner x f := fun h => hvw (h.trans hf)
      obtain ⟨hr,hp',hq'⟩ := (cluster_drawing_adj_iff x hw v f hv p q hp hq).mp ha
      exact Or.inr ⟨f,hf,hr.symm,hq',hp'⟩
    · have hw' : w≠SatDockCorridors.owner x e := fun h => hvw (he.symm.trans h.symm)
      obtain ⟨hr,hq',hp'⟩ := (cluster_drawing_adj_iff x hw w e hw' q p hq hp).mp ha.symm
      exact Or.inl ⟨e,he,hr.symm,hp',hq'⟩
    · have hef : e≠f := fun h => hvw (he.symm.trans ((congrArg (SatDockCorridors.owner x) h).trans hf))
      exact False.elim ((pairwise_apart x hw e f hef).2 p hp q hq ha)
  · rintro (⟨e,he,hr,rfl,rfl⟩|⟨e,he,hr,rfl,rfl⟩)
    · rw [← hr]
      exact (between x hw e).tip_adjacent
    · rw [← hr]
      exact (between x hw e).tip_adjacent.symm

end GridHardness.SatCompleteRegions
