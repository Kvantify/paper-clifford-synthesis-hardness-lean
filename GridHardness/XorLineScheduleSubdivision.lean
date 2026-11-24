/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.MandatoryArcSubdivision

/-!
# XOR Line Schedule Subdivision

Simultaneously subdivide distinct compulsory arc sources by two fresh
vertices each. The constructor keeps the identities of all old vertices.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule.Subdivision

variable {V I : Type*}
abbrev Vertex (V I : Type*) := V ⊕ (I × Bool)

def Adj (D : V → V → Prop) (s t : I → V) : Vertex V I → Vertex V I → Prop
  | .inl u, .inl v => D u v ∧ ¬∃ i, u=s i ∧ v=t i
  | .inl u, .inr (i,b) => u=s i ∧ b=false
  | .inr (i,b), .inl v => b=true ∧ v=t i
  | .inr (i,b), .inr (j,c) => i=j ∧ b=false ∧ c=true

noncomputable def index (s : I → V) (v : V) : Option I :=
  by
    classical
    exact if h : ∃ i, s i=v then some h.choose else none

theorem index_some (s : I → V) (hs : Function.Injective s) (i : I) :
    index s (s i)=some i := by
  classical
  simp only [index, dite_eq_left (show ∃ j, s j=s i from ⟨i,rfl⟩)]
  congr 1
  exact hs (Exists.choose_spec (show ∃ j, s j=s i from ⟨i,rfl⟩))

theorem of_index_some (s : I → V) (v : V) (i : I) (h : index s v =some i) : s i=v := by
  classical
  unfold index at h
  split at h
  · rename_i hv
    have he := Option.some.inj h
    exact he ▸ hv.choose_spec
  · contradiction

theorem of_index_none (s : I → V) (v : V) (h : index s v =none) (i : I) : v≠s i := by
  intro he
  classical
  have hv : ∃ j, s j=v := ⟨i,he.symm⟩
  simp [index,hv] at h

noncomputable def expand (s t : I → V) (next : V → V) : Vertex V I → Vertex V I
  | .inl v => match index s v with | none => .inl (next v) | some i => .inr (i,false)
  | .inr (i,false) => .inr (i,true)
  | .inr (i,true) => .inl (t i)

theorem expand_source (s t : I → V) (hs : Function.Injective s) (next : V → V) (i : I) :
    expand s t next (.inl (s i))=.inr (i,false) := by simp [expand,index_some s hs]

theorem expand_oneOrbit (s t : I → V) (hs : Function.Injective s) (next : V → V)
    (ho : OneOrbit next) (hst : ∀ i, next (s i) =t i) : OneOrbit (expand s t next) := by
  apply ho.expand Sum.inl
  · intro v
    cases hi : index s v with
    | none => exact ⟨1,by simp [expand,hi]⟩
    | some i =>
      have hv := of_index_some s v i hi
      subst v
      rw [hst]
      exact (show StepReach (expand s t next) (.inl (s i)) (.inr (i,false)) from
        ⟨1,expand_source s t hs next i⟩).trans
        ((show StepReach (expand s t next) (.inr (i,false)) (.inr (i,true)) from ⟨1,rfl⟩).trans
          ⟨1,rfl⟩)
  · intro v
    rcases v with v | ⟨i,b⟩
    · exact ⟨v,StepReach.refl _ _⟩
    · cases b
      · exact ⟨t i,(show StepReach (expand s t next) (.inr (i,false)) (.inr (i,true)) from
          ⟨1,rfl⟩).trans ⟨1,rfl⟩⟩
      · exact ⟨t i,⟨1,rfl⟩⟩
  · intro v
    rcases v with v | ⟨i,b⟩
    · exact ⟨v,StepReach.refl _ _⟩
    · cases b
      · exact ⟨s i,⟨1,expand_source s t hs next i⟩⟩
      · exact ⟨s i,(show StepReach (expand s t next) (.inl (s i)) (.inr (i,false)) from
          ⟨1,expand_source s t hs next i⟩).trans ⟨1,rfl⟩⟩

theorem expand_adj (D : V → V → Prop) (s t : I → V) (next : V → V)
    (ha : ∀ v, D v (next v)) : ∀ v, Adj D s t v (expand s t next v) := by
  rintro (v | ⟨i,b⟩)
  · cases hi : index s v with
    | none =>
      simp only [expand,hi,Adj]
      refine ⟨ha v,?_⟩
      rintro ⟨i,hv,_⟩
      exact of_index_none s v hi i hv
    | some i =>
      simp only [expand,hi,Adj]
      exact ⟨(of_index_some s v i hi).symm,trivial⟩
  · cases b <;> simp [expand,Adj]

def project (s : I → V) : Vertex V I → V
  | .inl v => v
  | .inr (i,_) => s i

noncomputable def contract (s t : I → V) (step : Vertex V I → Vertex V I) (v : V) : V :=
  match index s v with | none => project s (step (.inl v)) | some i => t i

theorem contract_source (s t : I → V) (hs : Function.Injective s)
    (step : Vertex V I → Vertex V I) (i : I) : contract s t step (s i)=t i := by
  simp [contract,index_some s hs]

theorem source_step (D : V → V → Prop) (s t : I → V)
    (step : Equiv.Perm (Vertex V I)) (ha : ∀ v, Adj D s t v (step v)) (i : I) :
    step (.inl (s i))=.inr (i,false) := by
  obtain ⟨v,hv⟩ := step.surjective (.inr (i,false))
  have hh := ha v
  rw [hv] at hh
  rcases v with v | ⟨j,b⟩
  · exact hh.1 ▸ hv
  · exact False.elim (Bool.false_ne_true hh.2.2)

theorem step_projects (D : V → V → Prop) (s t : I → V) (hs : Function.Injective s)
    (step : Equiv.Perm (Vertex V I)) (ha : ∀ v, Adj D s t v (step v)) (v : Vertex V I) :
    project s (step v)=project s v ∨
      project s (step v)=contract s t step (project s v) := by
  rcases v with v | ⟨i,b⟩
  · cases hi : index s v with
    | none => exact Or.inr (by simp [project,contract,hi])
    | some i =>
      have hv := of_index_some s v i hi
      subst v
      rw [source_step D s t step ha i]
      exact Or.inl rfl
  · have hh := ha (.inr (i,b))
    generalize he : step (.inr (i,b))=w at hh ⊢
    rcases w with w | ⟨j,c⟩
    · exact Or.inr (by simpa only [project,contract_source s t hs step i] using hh.2)
    · exact Or.inl (congrArg s hh.1.symm)

theorem contract_adj (D : V → V → Prop) (s t : I → V) (hst : ∀ i, D (s i) (t i))
    (step : Equiv.Perm (Vertex V I)) (ha : ∀ v, Adj D s t v (step v)) (v : V) :
    D v (contract s t step v) := by
  cases hi : index s v with
  | none =>
    simp only [contract,hi]
    have hh := ha (.inl v)
    generalize he : step (.inl v)=w at hh ⊢
    rcases w with w | ⟨i,b⟩
    · exact hh.1
    · exact False.elim (of_index_none s v hi i hh.1)
  | some i =>
    simp only [contract,hi]
    rw [← of_index_some s v i hi]
    exact hst i

/-- A finite simultaneous subdivision, derived from actual unique outgoing
arcs rather than from a promised cycle traversal. -/
theorem hamiltonian_iff [Finite V] [Finite I] (D : V → V → Prop) (s t : I → V)
    (hs : Function.Injective s) (hst : ∀ i, D (s i) (t i))
    (hout : ∀ i v, D (s i) v → v =t i) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (Adj D s t) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype (Vertex V I) := inferInstanceAs (Fintype (V ⊕ (I × Bool)))
  constructor
  · rintro ⟨next,ho,ha⟩
    have he := expand_oneOrbit s t hs next ho (fun i => hout i _ (ha (s i)))
    exact ⟨Equiv.ofBijective _ he.bijective,he,expand_adj D s t next ha⟩
  · rintro ⟨step,ho,ha⟩
    have hc := ho.project (project s) (fun v => ⟨.inl v,rfl⟩)
      (step_projects D s t hs step ha)
    exact ⟨Equiv.ofBijective _ hc.bijective,hc,contract_adj D s t hst step ha⟩

@[simp] theorem vertex_count [Fintype V] [Fintype I] :
    Fintype.card (Vertex V I)=Fintype.card V+2*Fintype.card I := by
  simp [Vertex,Fintype.card_sum,Fintype.card_prod,Nat.mul_comm]

end GridHardness.XorLineSchedule.Subdivision
