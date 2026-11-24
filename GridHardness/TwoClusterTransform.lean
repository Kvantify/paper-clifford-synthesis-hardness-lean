/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoClusterAssembly
public import GridHardness.SignedTentacleTransform

/-!
# Two Cluster Transform

A common signed lattice placement transports the exact interfaces of
two clusters and their joining tentacle. In particular no selected edge
set is substituted for the actual induced-grid boundary.
-/

@[expose] public section

namespace GridHardness.TwoClusterAssembly
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

@[simp] theorem cluster_comp (f g : Frame) :
    cluster (f.comp g)=(cluster g).image f.map := f.image_comp g _

@[simp] theorem corner_comp (f g : Frame) (s : Fin 4) :
    corner (f.comp g) s=f.map (corner g s) := f.map_comp g _

@[simp] theorem mate_comp (f g : Frame) (s : Fin 4) :
    mate (f.comp g) s=f.map (mate g s) := f.map_comp g _

/-- The ordered boundary edge set is transported exactly by any signed frame. -/
theorem boundary_transform (f : Frame) (S T : Finset Point) :
    boundary (S.image f.map) (T.image f.map)=
      (boundary S T).image (fun e => (f.map e.1,f.map e.2)) := by
  ext e
  rcases e with ⟨p,q⟩
  constructor
  · intro h
    obtain ⟨hm,ha⟩ := Finset.mem_filter.mp h
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hm
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hu,hv⟩,(f.adj_iff u v).mp ha⟩,rfl⟩
  · intro h
    obtain ⟨⟨u,v⟩,hm,he⟩ := Finset.mem_image.mp h
    cases he
    obtain ⟨hm,ha⟩ := Finset.mem_filter.mp hm
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨u,hu,rfl⟩,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩,
      (f.adj_iff u v).mpr ha⟩

/-- An exact two-edge boundary follows from its pointwise characterization. -/
theorem boundary_eq_pair {S T : Finset Point} {a b c d : Point}
    (ha : a ∈S) (hb : b ∈T) (hc : c ∈S) (hd : d ∈T)
    (h : ∀ u ∈S, ∀ v ∈T, lattice.Adj u v ↔ (u =a ∧ v =b) ∨ (u =c ∧ v =d)) :
    boundary S T={(a,b),(c,d)} := by
  ext ⟨u,v⟩
  simp only [boundary,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  constructor
  · rintro ⟨hm,he⟩
    have hm := Finset.mem_product.mp hm
    exact (h u hm.1 v hm.2).mp he
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨Finset.mem_product.mpr ⟨ha,hb⟩,(h _ ha _ hb).mpr (Or.inl ⟨rfl,rfl⟩)⟩
    · exact ⟨Finset.mem_product.mpr ⟨hc,hd⟩,(h _ hc _ hd).mpr (Or.inr ⟨rfl,rfl⟩)⟩

/-- Both cluster interfaces, including the single recipient edge, survive
translation, reflection and interchange of the coordinate axes. -/
theorem Between.transform (f : Frame) {d : Drawing} {g h : Frame} {s t : Fin 4}
    (hv : Between d g h s t) :
    Between (Drawing.transform f d) (f.comp g) (f.comp h) s t := by
  rcases hv with ⟨hgd,hhd,hgh,hsep,hleft,hright⟩
  unfold Between
  simp only [cluster_comp,Drawing.transform_points]
  refine ⟨(Finset.disjoint_image f.injective).mpr hgd,
    (Finset.disjoint_image f.injective).mpr hhd,
    (Finset.disjoint_image f.injective).mpr hgh,?_,?_,?_⟩
  · rintro a ha b hb hab
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    exact hsep u hu v hv ((f.adj_iff u v).mp hab)
  · rw [boundary_transform,hleft]
    simp only [Finset.image_insert,Finset.image_singleton,corner_comp,mate_comp,
      Drawing.transform_start]
  · rw [boundary_transform,hright]
    simp only [Finset.image_singleton,corner_comp,Drawing.transform_tip]

end GridHardness.TwoClusterAssembly
