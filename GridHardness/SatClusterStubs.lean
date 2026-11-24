/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteDirections
public import GridHardness.SatBipartiteCorrectness
public import GridHardness.NineClusterDockGeometry
public import GridHardness.GridAssemblyLocal

/-!
# SAT Cluster Stubs

Three-slot families of local owner stubs indexed by the actual
incidences of the bipartite SAT graph. Every incidence occurs exactly once,
on its proved cardinal side. These length-six straight stubs form valid
local arms; they are not the completed tentacles between distant clusters.
The finite slot assignment is semantic and uses classical choice.
-/

@[expose] public section

namespace GridHardness.SatClusterStubs
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open SatBipartiteDrawing SatBipartiteDirections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Each incidence identifies its opposite endpoint, an actual graph neighbor. -/
def neighbor (x : SatTy.denote) (v : Vertex x) (i : Incidence x v) :
    {w : Vertex x // (graph x).Adj v w} := by
  rcases i with ⟨⟨e,b⟩,hi⟩
  refine ⟨endpointVertex x e (!b),?_⟩
  cases b
  · change source x e=v at hi
    rw [← hi]
    exact SatBipartiteEdges.edge_adj x e
  · change target x e=v at hi
    rw [← hi]
    exact (SatBipartiteEdges.edge_adj x e).symm

/-- The simple edge catalogue makes opposite endpoints distinguish incidences. -/
theorem neighbor_injective (x : SatTy.denote) (v : Vertex x) :
    Function.Injective (neighbor x v) := by
  rintro ⟨⟨e,b⟩,hi⟩ ⟨⟨f,c⟩,hj⟩ he
  have ho := congrArg Subtype.val he
  change endpointVertex x e (!b)=endpointVertex x f (!c) at ho
  have hv : endpointVertex x e b=endpointVertex x f c := hi.trans hj.symm
  have hef : e=f := by
    apply SatBipartiteEdges.unordered_endpoints_injective x e f
    cases b <;> cases c
    · exact Or.inl ⟨hv,ho⟩
    · exact Or.inr ⟨hv,ho⟩
    · exact Or.inr ⟨ho,hv⟩
    · exact Or.inl ⟨ho,hv⟩
  subst f
  have hbc : b=c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (endpoints_ne x e hv)
    · exact False.elim (endpoints_ne x e hv.symm)
    · rfl
  exact Subtype.ext (Prod.ext rfl hbc)

theorem incidence_card_le_three (x : SatTy.denote) (v : Vertex x) :
    Nat.card (Incidence x v)≤3 :=
  (Nat.card_le_card_of_injective (neighbor x v) (neighbor_injective x v)).trans
    (SatBipartiteCorrectness.neighbor_card_le_three x v)

/-- Reserve one of the three arm slots for each actual incidence. -/
noncomputable def slot (x : SatTy.denote) (v : Vertex x) : Incidence x v ↪ Fin 3 := by
  letI := Fintype.ofFinite (Incidence x v)
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_fin] using incidence_card_le_three x v))

/-- The optional incidence stored at an arm slot. -/
noncomputable def atSlot (x : SatTy.denote) (v : Vertex x) (k : Fin 3) :
    Option (Incidence x v) := by
  classical
  exact if h : ∃ i, slot x v i=k then some (Classical.choose h) else none

theorem atSlot_eq_some_iff (x : SatTy.denote) (v : Vertex x) (k : Fin 3)
    (i : Incidence x v) : atSlot x v k=some i ↔ slot x v i=k := by
  classical
  unfold atSlot
  split_ifs with h
  · constructor
    · intro he
      have hchoose := Classical.choose_spec h
      exact (congrArg (slot x v) (Option.some.inj he)).symm.trans hchoose
    · intro hi
      apply congrArg some
      exact (slot x v).injective ((Classical.choose_spec h).trans hi.symm)
  · constructor
    · intro he; cases he
    · intro hi; exact False.elim (h ⟨i,hi⟩)

@[simp] theorem atSlot_slot (x : SatTy.denote) (v : Vertex x) (i : Incidence x v) :
    atSlot x v (slot x v i)=some i := (atSlot_eq_some_iff x v _ i).mpr rfl

noncomputable def side (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i : Incidence x v) : Fin 4 :=
  NineClusterDockGeometry.sideOfDirection (direction x hw i.val.1 i.val.2)

theorem side_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    Function.Injective (side x hw v) :=
  NineClusterDockGeometry.sideOfDirection_injective.comp (incident_directions_injective x hw v)

/-- The initial straight portion of an owner tentacle. -/
noncomputable def stub (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i : Incidence x v) : Drawing :=
  .base (NineClusterAttachment.dock true (side x hw v i)) 6

/-- Empty arm slots remain empty, while every actual incidence gets its stub. -/
noncomputable def arms (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : GridAssembly.Arms := fun k =>
  (atSlot x v k).map (fun i => (side x hw v i,stub x hw v i))

@[simp] theorem arms_slot (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i : Incidence x v) :
    arms x hw v (slot x v i)=some (side x hw v i,stub x hw v i) := by
  simp [arms]

/-- Every occupied arm comes from one uniquely determined actual incidence. -/
theorem arms_eq_some_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (k : Fin 3) (s : Fin 4) (d : Drawing) :
    arms x hw v k=some (s,d) ↔
      ∃ i : Incidence x v, slot x v i=k ∧ side x hw v i=s ∧ stub x hw v i=d := by
  classical
  unfold arms
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    exact ⟨i,(atSlot_eq_some_iff x v k i).mp hi,
      congrArg Prod.fst he,congrArg Prod.snd he⟩
  · rintro ⟨i,hi,hs,hd⟩
    exact ⟨i,(atSlot_eq_some_iff x v k i).mpr hi,Prod.ext hs hd⟩

/-- A given incidence's stub appears at exactly its reserved slot. -/
theorem arms_occurrence_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (k : Fin 3) (i : Incidence x v) :
    arms x hw v k=some (side x hw v i,stub x hw v i) ↔ k=slot x v i := by
  constructor
  · intro h
    obtain ⟨j,hj,hside,_⟩ := (arms_eq_some_iff x hw v k _ _).mp h
    have hji := side_injective x hw v hside
    subst j
    exact hj.symm
  · rintro rfl
    exact arms_slot x hw v i

/-- Every actual incidence has one and only one occupied arm slot. -/
theorem incidence_present_unique (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i : Incidence x v) :
    ∃! k, arms x hw v k=some (side x hw v i,stub x hw v i) :=
  ⟨slot x v i,arms_slot x hw v i,fun k hk => (arms_occurrence_iff x hw v k i).mp hk⟩

/-- Incidences occupy distinct sides, so all selected length-six owner
stubs satisfy the existing three-arm geometric validity conditions. -/
theorem arms_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    (arms x hw v).Valid := by
  constructor
  · intro k
    cases hk : atSlot x v k with
    | none => simp [arms,hk,GridAssembly.Arm.Valid]
    | some i =>
      change GridAssembly.Arm.Valid ((atSlot x v k).map _)
      rw [hk]
      exact ⟨by change 3≤6; decide,rfl⟩
  · intro k l hkl
    cases hk : atSlot x v k with
    | none => simp [arms,hk,GridAssembly.Arm.Apart]
    | some i =>
      cases hl : atSlot x v l with
      | none => simp [arms,hl,GridAssembly.Arm.Apart]
      | some j =>
        have hij : i≠j := by
          intro he
          apply hkl
          exact ((atSlot_eq_some_iff x v k i).mp hk).symm.trans
            ((congrArg (slot x v) he).trans ((atSlot_eq_some_iff x v l j).mp hl))
        have hs : side x hw v i≠side x hw v j := fun h => hij (side_injective x hw v h)
        change GridAssembly.Arm.Apart ((atSlot x v k).map _) ((atSlot x v l).map _)
        rw [hk,hl]
        exact ⟨hs,NineClusterDockGeometry.docks_apart true true _ _ hs 6 6⟩

end GridHardness.SatClusterStubs
