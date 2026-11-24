/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCodeAdequacy

/-!
# XOR Wire Code

Identify compiled XOR wire arcs with the arcs of the mathematical replacement graph.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorWireCode
open CliffordComplexity

theorem program_arc_iff (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ ((program L).eval x).2.1 ↔
      XorWire.network (outside x) (enter x) (leave x) (link x) (L.eval x).length a b := by
  change _ ∈ outsideCode.eval x ++ ((internalCode L).eval x ++
    ((wireLinksCode L).eval x ++ ((enterCode L).eval x ++
      ((leaveCode L).eval x ++ (linksCode L).eval x)))) ↔ _
  rw [← List.append_assoc]
  simp only [List.mem_append]
  rw [numbered_outside,numbered_internal,numbered_wireLinks,numbered_enter,numbered_leave,numbered_link]
  constructor
  · rintro ((h | h) | h | h | h | h)
    · obtain ⟨u,v,hm,rfl,rfl⟩ := h
      exact hm
    · obtain ⟨c,s,e,rfl,rfl⟩ := h
      exact Or.inl ⟨rfl,Or.inl ⟨rfl,e,rfl⟩⟩
    · obtain ⟨c,i,h | h⟩ := h
      · rcases h with ⟨rfl,rfl⟩
        exact Or.inl ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)⟩
      · rcases h with ⟨rfl,rfl⟩
        exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨rfl,rfl,rfl⟩)⟩
    · obtain ⟨u,c,s,hm,rfl,rfl⟩ := h
      exact ⟨(),s,hm,rfl⟩
    · obtain ⟨u,c,s,hm,rfl,rfl⟩ := h
      exact ⟨(),s,hm,rfl⟩
    · obtain ⟨c,d,s,t,hne,hm,rfl,rfl⟩ := h
      exact Or.inr ⟨hne,(),s,(),t,hm,rfl,rfl⟩
  · intro h
    cases a with
    | inl u =>
      cases b with
      | inl v => exact Or.inl (Or.inl ⟨u,v,h,rfl,rfl⟩)
      | inr p =>
        rcases p with ⟨c,v⟩
        obtain ⟨⟨⟩,s,hs,rfl⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨u,c,s,hs,rfl,rfl⟩))
    | inr p =>
      rcases p with ⟨c,u⟩
      cases b with
      | inl v =>
        obtain ⟨⟨⟩,s,hs,rfl⟩ := h
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v,c,s,hs,rfl,rfl⟩)))
      | inr p =>
        rcases p with ⟨d,v⟩
        rcases h with ⟨hcd,huv⟩ | ⟨hcd,⟨⟩,s,⟨⟩,t,hm,hu,hv⟩
        · subst d
          rcases u with ⟨i,j⟩
          rcases v with ⟨k,l⟩
          rcases huv with ⟨hik,e,he⟩ | ⟨hik,hj,hl⟩ | ⟨hki,hj,hl⟩
          · dsimp at hik he
            subst k
            exact Or.inl (Or.inr ⟨c,i,e,
              congrArg (wire L x c i) (congrArg Prod.fst he).symm,
              congrArg (wire L x c i) (congrArg Prod.snd he).symm⟩)
          · dsimp at hik hj hl
            subst j
            subst l
            let q : Fin (L.eval x).length := ⟨i.val,by have := k.isLt; omega⟩
            have hqi : q.castSucc = i := Fin.ext rfl
            have hqk : q.succ = k := Fin.ext hik
            exact Or.inr (Or.inl ⟨c,q,Or.inl
              ⟨congrArg (fun z => wire L x c z 0) hqi.symm,
               congrArg (fun z => wire L x c z 3) hqk.symm⟩⟩)
          · dsimp at hki hj hl
            subst j
            subst l
            let q : Fin (L.eval x).length := ⟨k.val,by have := i.isLt; omega⟩
            have hqk : q.castSucc = k := Fin.ext rfl
            have hqi : q.succ = i := Fin.ext hki
            exact Or.inr (Or.inl ⟨c,q,Or.inr
              ⟨congrArg (fun z => wire L x c z 7) hqi.symm,
               congrArg (fun z => wire L x c z 4) hqk.symm⟩⟩)
        · subst u
          subst v
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,d,s,t,hcd,hm,rfl,rfl⟩)))

noncomputable def decodeEquiv (L : Code InputTy NatListTy) (x : InputTy.denote) :
    V L x ≃ Fin ((program L).eval x).1.length :=
  (numbering L x).equivFin.trans (finCongr (vertices_length L x).symm)

@[simp] theorem decodeEquiv_val (L : Code InputTy NatListTy) (x : InputTy.denote) (a : V L x) :
    (decodeEquiv L x a).val = (numbering L x).num a := rfl

theorem compiled_arc_iff (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((decodeEquiv L x a).val,(decodeEquiv L x b).val) ∈ ((program L).eval x).2.1 ↔
      XorWire.network (outside x) (enter x) (leave x) (link x) (L.eval x).length a b :=
  program_arc_iff L x a b

theorem program_nonempty (L : Code InputTy NatListTy) (x : InputTy.denote) :
    0 < ((program L).eval x).1.length ↔ 0 < x.1.1.length + x.2.1.length := by
  change 0 < ((vertices L).eval x).length ↔ _
  rw [vertices_length]
  have hk : 0 < ((L.eval x).length + 1) * 8 := by omega
  by_cases hc : x.2.1.length = 0
  · simp [hc]
  · have hm := Nat.mul_pos (Nat.pos_of_ne_zero hc) hk
    omega

/-- Exact directed-Hamiltonicity interpretation of the compiled graph.
The guard handles the fully empty input independently of wire length. -/
theorem program_interpretation (L : Code InputTy NatListTy) (x : InputTy.denote) :
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE ((program L).eval x) ↔
      0 < x.1.1.length + x.2.1.length ∧
      PathCover.Hamiltonian (XorWire.network (outside x) (enter x) (leave x) (link x) (L.eval x).length) := by
  let e := decodeEquiv L x
  constructor
  · rintro ⟨hn,next,ho,ha⟩
    refine ⟨(program_nonempty L x).mp hn,e.trans (next.trans e.symm),?_,?_⟩
    · exact ho.transport e.symm (by intro v; simp)
    · intro v
      apply (compiled_arc_iff L x v _).mp
      simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply] using ha (e v)
  · rintro ⟨hn,next,ho,ha⟩
    refine ⟨(program_nonempty L x).mpr hn,e.symm.trans (next.trans e),?_,?_⟩
    · exact ho.transport e (by intro v; simp)
    · intro w
      obtain ⟨v,rfl⟩ := e.surjective w
      simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using
        (compiled_arc_iff L x v (next v)).mpr (ha v)

def sourceCode : Code InputTy GraphTy := program (.const NatListTy [])
def targetCode : Code InputTy GraphTy := program stretches

/-- The source language is the actual encoded one-section-per-cell graph. -/
def SOURCE_HAMILTONIAN : Problem InputTy.denote := fun x =>
  DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE (sourceCode.eval x)

theorem code_correct (x : InputTy.denote) : SOURCE_HAMILTONIAN x ↔
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE (targetCode.eval x) := by
  change DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE ((program (.const NatListTy [])).eval x) ↔ _
  rw [program_interpretation, targetCode, program_interpretation]
  exact and_congr_right (fun _ =>
    XorWire.network_stretch_iff (outside x) (enter x) (leave x) (link x) 0 _)

def certified : CertifiedReduction SOURCE_HAMILTONIAN
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE := ⟨targetCode,code_correct⟩

theorem source_vertex_count (x : InputTy.denote) :
    (sourceCode.eval x).1.length = x.1.1.length + x.2.1.length * 8 := by
  exact vertices_length (.const NatListTy []) x

theorem target_vertex_count (x : InputTy.denote) :
    (targetCode.eval x).1.length = x.1.1.length + x.2.1.length * ((x.2.2.1.length + 1) * 8) :=
  vertices_length stretches x

def certifiedBipartite : CertifiedReduction SOURCE_HAMILTONIAN
    DirectedToBipartite.BIPARTITE_HAMILTONIAN_CYCLE :=
  certified.comp DirectedToBipartite.certifiedBipartite

end GridHardness.XorWireCode
