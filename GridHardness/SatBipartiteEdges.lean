/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartitePlacement

/-!
# SAT Bipartite Edges

An exact edge catalogue for the undirected bipartite graph obtained
by replacing each actual SAT vertex with a path of four vertices. The
catalogue includes the three internal edges and one external edge for
each actual directed arc.
-/

@[expose] public section

namespace GridHardness.SatBipartiteEdges
open CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatBipartitePlacement.Vertex

/-- The actual undirected graph of the directed-to-bipartite reduction. -/
def graph (x : SatTy.denote) : SimpleGraph (Vertex x) :=
  DirectedToBipartite.graph (SatClauseOrder.graph (finiteFormula x)).adj

abbrev Edge (x : SatTy.denote) :=
  (SatCompleteDrawing.Vertex x × Fin 3) ⊕ SatCompleteDrawing.Arc x

def source (x : SatTy.denote) : Edge x → Vertex x
  | .inl (v,i) => (v,i.castSucc)
  | .inr a => (SatCompleteDrawing.source x a,3)

def target (x : SatTy.denote) : Edge x → Vertex x
  | .inl (v,i) => (v,i.succ)
  | .inr a => (SatCompleteDrawing.target x a,0)

theorem edge_adj (x : SatTy.denote) (e : Edge x) :
    (graph x).Adj (source x e) (target x e) := by
  cases e with
  | inl p => exact Or.inl ⟨rfl,Or.inl rfl⟩
  | inr a => exact Or.inr (Or.inl ⟨rfl,rfl,a.property⟩)

/-- The finite catalogue contains every actual edge in either orientation. -/
theorem adjacency_iff (x : SatTy.denote) (u v : Vertex x) :
    (graph x).Adj u v ↔ ∃ e : Edge x,
      (source x e=u ∧ target x e=v) ∨ (source x e=v ∧ target x e=u) := by
  constructor
  · rcases u with ⟨u,i⟩
    rcases v with ⟨v,j⟩
    rintro (⟨huv,hij | hji⟩ | ⟨hi,hj,ha⟩ | ⟨hi,hj,ha⟩)
    · dsimp only at huv hij
      subst v
      let k : Fin 3 := ⟨i.val,by have := j.isLt; omega⟩
      refine ⟨.inl (u,k),Or.inl ⟨?_,?_⟩⟩
      · exact Prod.ext rfl (Fin.ext rfl)
      · exact Prod.ext rfl (Fin.ext hij)
    · dsimp only at huv hji
      subst v
      let k : Fin 3 := ⟨j.val,by have := i.isLt; omega⟩
      refine ⟨.inl (u,k),Or.inr ⟨?_,?_⟩⟩
      · exact Prod.ext rfl (Fin.ext rfl)
      · exact Prod.ext rfl (Fin.ext hji)
    · dsimp only at hi hj
      subst i
      subst j
      exact ⟨.inr ⟨(u,v),ha⟩,Or.inl ⟨rfl,rfl⟩⟩
    · dsimp only at hi hj
      subst i
      subst j
      exact ⟨.inr ⟨(v,u),ha⟩,Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact edge_adj x e
    · exact (edge_adj x e).symm

/-- Distinct catalogue indices never have the same ordered endpoints. -/
theorem endpoints_injective (x : SatTy.denote) :
    Function.Injective (fun e : Edge x => (source x e,target x e)) := by
  intro e f he
  have hs := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  cases e with
  | inl p =>
    rcases p with ⟨v,i⟩
    cases f with
    | inl q =>
      rcases q with ⟨w,j⟩
      have hv := congrArg Prod.fst hs
      have hi := congrArg (fun p : Vertex x => p.2.val) hs
      exact congrArg Sum.inl (Prod.ext hv (Fin.ext hi))
    | inr a =>
      have hi := congrArg (fun p : Vertex x => p.2.val) hs
      change i.val=3 at hi
      have := i.isLt
      omega
  | inr a =>
    cases f with
    | inl p =>
      rcases p with ⟨v,i⟩
      have hi := congrArg (fun p : Vertex x => p.2.val) hs
      change 3=i.val at hi
      have := i.isLt
      omega
    | inr b =>
      have ha := congrArg Prod.fst hs
      have hb := congrArg Prod.fst ht
      exact congrArg Sum.inr (Subtype.ext (Prod.ext ha hb))

/-- Catalogue orientations cannot reverse each other. The four-position
indices distinguish both internal and external directions. -/
theorem not_reversed (x : SatTy.denote) (e f : Edge x) :
    ¬ (source x e=target x f ∧ target x e=source x f) := by
  rintro ⟨hs,ht⟩
  have hi := congrArg (fun p : Vertex x => p.2.val) hs
  have hj := congrArg (fun p : Vertex x => p.2.val) ht
  cases e with
  | inl p =>
    rcases p with ⟨v,i⟩
    cases f with
    | inl q =>
      rcases q with ⟨w,j⟩
      change i.val=j.val+1 at hi
      change i.val+1=j.val at hj
      omega
    | inr a =>
      change i.val=0 at hi
      change i.val+1=3 at hj
      omega
  | inr a =>
    cases f with
    | inl p =>
      rcases p with ⟨v,i⟩
      change 3=i.val+1 at hi
      change 0=i.val at hj
      omega
    | inr b =>
      change (3:Nat)=0 at hi
      omega

/-- Each unordered actual edge has a unique catalogue index. -/
theorem unordered_endpoints_injective (x : SatTy.denote) (e f : Edge x)
    (h : (source x e =source x f ∧ target x e =target x f) ∨
      (source x e =target x f ∧ target x e =source x f)) : e=f := by
  rcases h with h | h
  · exact endpoints_injective x (Prod.ext h.1 h.2)
  · exact False.elim (not_reversed x e f h)

end GridHardness.SatBipartiteEdges
