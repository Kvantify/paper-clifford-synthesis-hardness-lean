/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyLocal
public import GridHardness.RegionExpansion

/-!
# Grid Assembly Partition

Restrict lattice routes to a larger induced finite grid. This retains
their exact regional supports, which are the inputs needed for expansion.
-/

public section

namespace GridHardness.GridAssembly
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

theorem lift_route {S T : Finset Point} (hsub : S ⊆ T) {a b : Point}
    (ha : a ∈ S) (hb : b ∈ S) (hr : HasRoute S a b) :
    ∃ p : (finiteGrid T).Walk ⟨a, hsub ha⟩ ⟨b, hsub hb⟩,
      p.IsPath ∧ ∀ v, v ∈ p.support ↔ v.val ∈ S := by
  obtain ⟨p, hp⟩ := (hasRoute_iff_hamiltonian ha hb).mp hr
  let f : finiteGrid S →g finiteGrid T :=
    ⟨fun v => ⟨v.val, hsub v.property⟩, fun h => h⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun x : T => x.val) he)
  refine ⟨p.map f, hp.isPath.map hf, ?_⟩
  intro v
  simp only [Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨w, _, rfl⟩
    exact w.property
  · intro hv
    exact ⟨⟨v.val, hv⟩, hp.mem_support _, rfl⟩

end GridHardness.GridAssembly
