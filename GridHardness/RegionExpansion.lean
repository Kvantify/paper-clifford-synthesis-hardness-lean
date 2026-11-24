/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GadgetReplacement
public import GridHardness.RegionContraction

/-!
# Region Expansion

Expand a spanning cycle through a partition into actual simple walks.
The path-cover equivalence is derived from exact walk supports. The final
port theorem is generic: applications must prove its local route and graph
interface hypotheses for their constructed coordinate sets.
-/

@[expose] public section

namespace GridHardness.RegionExpansion
open SimpleGraph SimpleGraph.Walk PathCover
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

section Cover
variable {V C : Type*} {G : SimpleGraph V} (label : V → C) {a b : C → V}
variable (p : ∀ c, G.Walk (a c) (b c)) (hp : ∀ c, (p c).IsPath)
variable (hcover : ∀ c v, v ∈ (p c).support ↔ label v = c)

def vertex : Blocks (fun c => (p c).length) → V := fun ⟨c, i⟩ => (p c).getVert i.val

include label hp hcover

/-- Exact fiber supports and path simplicity give a bijection from all
indexed path positions to the ambient graph's vertices. -/
theorem vertex_bijective : Function.Bijective (vertex p) := by
  constructor
  · rintro ⟨c, i⟩ ⟨d, j⟩ he
    have hc := (hcover c _).mp ((p c).getVert_mem_support i.val)
    have hd := (hcover d _).mp ((p d).getVert_mem_support j.val)
    have hcd : c = d := hc.symm.trans ((congrArg label he).trans hd)
    subst d
    have hij : i = j := Fin.ext ((hp c).getVert_injOn
      (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) he)
    cases hij
    rfl
  · intro v
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp ((hcover (label v) v).mpr rfl)
    exact ⟨⟨label v, ⟨i, Nat.lt_succ_of_le hil⟩⟩, hi⟩

noncomputable def cover : PathCover.Cover C V where
  size := fun c => (p c).length
  equiv := Equiv.ofBijective (vertex p) (vertex_bijective label p hp hcover)

@[simp] theorem cover_apply (c : C) (i : Fin ((p c).length + 1)) :
    (cover label p hp hcover).equiv ⟨c, i⟩ = (p c).getVert i.val := rfl

@[simp] theorem cover_first (c : C) : (cover label p hp hcover).first c = a c :=
  (p c).getVert_zero

@[simp] theorem cover_finish (c : C) : (cover label p hp hcover).finish c = b c :=
  (p c).getVert_length

theorem cover_internalEdges : (cover label p hp hcover).InternalEdges G.Adj := by
  intro c i
  exact (p c).adj_getVert_succ i.isLt

/-- Actual neighboring endpoints join the regional paths into one spanning
successor orbit. This does not merely construct a cycle cover. -/
theorem expand_oneOrbit [Finite C] (next : Equiv.Perm C) (ho : OneOrbit next)
    (he : ∀ c, G.Adj (b c) (a (next c))) : PathCover.Hamiltonian G.Adj := by
  apply (cover label p hp hcover).expand_hamiltonian G.Adj (cover_internalEdges label p hp hcover)
  refine ⟨next, ho, ?_⟩
  intro c
  simpa only [PathCover.Cover.Wiring, cover_first, cover_finish] using he c

/-- Conversion to mathlib's actual Hamiltonian-cycle predicate, including
the cardinality condition that rules out a doubled single edge. -/
theorem hamiltonianCycle_expand [Finite C] [Fintype V] [DecidableEq V]
    (hv : 3 ≤ Fintype.card V) (next : Equiv.Perm C) (ho : OneOrbit next)
    (he : ∀ c, G.Adj (b c) (a (next c))) :
    ∃ (v : V) (q : G.Walk v v), q.IsHamiltonianCycle :=
  (hamiltonianCycle_iff_oneOrbit G hv).mpr (expand_oneOrbit label p hp hcover next ho he)

end Cover

section Ports
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- Local routing at every distinct neighbor pair suffices for expansion.
The walks are actual ambient-graph paths covering exactly one label fiber;
applications must establish them, for example using the cluster-star theorem. -/
theorem hamiltonianCycle_expand_ports (G : SimpleGraph V) (H : SimpleGraph C)
    (label : V → C) (hs : Function.Surjective label) (hc : 3 ≤ Fintype.card C)
    (port : C → C → V)
    (hedge : ∀ c d, H.Adj c d → G.Adj (port c d) (port d c))
    (hroute : ∀ c d e, H.Adj c d → H.Adj c e → d ≠ e →
      ∃ p : G.Walk (port c d) (port c e), p.IsPath ∧
        ∀ v, v ∈ p.support ↔ label v = c)
    (hh : ∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := by
  classical
  obtain ⟨next, ho, ha⟩ := (hamiltonianCycle_iff_oneOrbit H hc).mp hh
  have hpred (c : C) : H.Adj c (next.symm c) := by
    simpa only [Equiv.apply_symm_apply] using (ha (next.symm c)).symm
  have hdistinct (c : C) : next.symm c ≠ next c := by
    intro he
    have he' := congrArg next he
    simp only [Equiv.apply_symm_apply] at he'
    exact ho.not_period_two hc c he'.symm
  choose paths hpath hcover using (fun c => hroute c (next.symm c) (next c)
    (hpred c) (ha c) (hdistinct c))
  apply hamiltonianCycle_expand label paths hpath hcover
    (hc.trans (Fintype.card_le_of_surjective label hs)) next ho
  intro c
  simpa only [Equiv.symm_apply_apply] using hedge c (next c) (ha c)

/-- A complete generic correspondence from local path routing and actual
subcubic inter-region edges. No planar or grid construction is asserted here. -/
theorem hamiltonianCycle_iff_of_subcubic_ports
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph C) [DecidableRel H.Adj]
    (label : V → C) (hs : Function.Surjective label) (hc : 3 ≤ Fintype.card C)
    (hd : ∀ c, H.degree c ≤ 3)
    (hinter : ∀ u v, G.Adj u v → label u ≠ label v → H.Adj (label u) (label v))
    (hunique : RegionContraction.UniqueBetween G label)
    (port : C → C → V)
    (hedge : ∀ c d, H.Adj c d → G.Adj (port c d) (port d c))
    (hroute : ∀ c d e, H.Adj c d → H.Adj c e → d ≠ e →
      ∃ p : G.Walk (port c d) (port c e), p.IsPath ∧
        ∀ v, v ∈ p.support ↔ label v = c) :
    (∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle) ↔
      ∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle :=
  ⟨RegionContraction.hamiltonianCycle_contract_of_subcubic G H label hs hc hd hinter hunique,
    hamiltonianCycle_expand_ports G H label hs hc port hedge hroute⟩

end Ports
end GridHardness.RegionExpansion
