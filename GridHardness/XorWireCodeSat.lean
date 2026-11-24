/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCodeSatProgram

/-!
# XOR Wire Code SAT

Specialize the vertex and cell numbering of XOR wire replacements to SAT graphs.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 300000

namespace GridHardness.XorWireCodeSat
open CliffordComplexity PlanarSatAssembly
open XorWireCode (InputTy NatListTy)

def outsideNumbering (n m : Nat) : Numbering (Outside n m) :=
  (Numbering.fin 3).sum (((Numbering.fin n).prod Numbering.bool).sum
    ((Numbering.fin m).prod (Numbering.fin 12)))
def cellNumbering (m : Nat) : Numbering (Occurrence m) :=
  (Numbering.fin m).prod (Numbering.fin 3)

@[simp] theorem outsideNumbering_size (n m : Nat) :
    (outsideNumbering n m).size = 3+n*2+m*12 := by
  simp [outsideNumbering,Nat.add_assoc]
@[simp] theorem cellNumbering_size (m : Nat) : (cellNumbering m).size = m*3 := rfl

theorem outsideNumbering_num {n m : Nat} (a : Outside n m) :
    (outsideNumbering n m).num a = (PlanarSatCode.numbering n m).num (outsideVertex a) := by
  rcases a with a | (a | a) <;> rfl

noncomputable def outerEquiv (x : SatTy.denote) :
    Outside ((vsOf x).length+1) x.length ≃ XorWireCode.Outer (assembly.eval x) :=
  (outsideNumbering _ _).equivFin.trans
    (finCongr ((outsideNumbering_size _ _).trans (outerVertices_length x).symm))
noncomputable def cellEquiv (x : SatTy.denote) :
    Occurrence x.length ≃ XorWireCode.Cell (assembly.eval x) :=
  (cellNumbering _).equivFin.trans (finCongr (cells_length x).symm)

@[simp] theorem outerEquiv_val (x : SatTy.denote) (a : Outside ((vsOf x).length +1) x.length) :
    (outerEquiv x a).val = (outsideNumbering _ _).num a := rfl
@[simp] theorem cellEquiv_val (x : SatTy.denote) (o : Occurrence x.length) :
    (cellEquiv x o).val = o.1.val*3+o.2.val := rfl

theorem outside_iff (x : SatTy.denote) (a b : Outside ((vsOf x).length +1) x.length) :
    XorWireCode.outside (assembly.eval x) (outerEquiv x a) (outerEquiv x b) ↔
      SatWireExpansion.outside (finiteFormula x) a b := by
  unfold XorWireCode.outside
  have pair_eval {s t u : Ty} (f : Code s t) (g : Code s u) (y : s.denote) :
      (Code.pair f g).eval y = (f.eval y, g.eval y) := rfl
  have he : (assembly.eval x).1.2.1 = outerEdges.eval x := by
    simp only [assembly, pair_eval]
  rw [he, mem_outerEdges]
  have ha := (outerEquiv x a).isLt
  have hb := (outerEquiv x b).isLt
  change (outerEquiv x a).val < (outerVertices.eval x).length at ha
  change (outerEquiv x b).val < (outerVertices.eval x).length at hb
  simp only [ha,hb,true_and,and_self]
  rw [outerEquiv_val x a, outerEquiv_val x b, outsideNumbering_num a,
    outsideNumbering_num b]
  exact PlanarSatCode.mem_edgesCode x (outsideVertex a) (outsideVertex b)

theorem enterPair_eval (x : SatTy.denote) (a : Outside ((vsOf x).length +1) x.length)
    (o : Occurrence x.length) (s : Bool) :
    enterPair.eval (x,((outerEquiv x a).val,((cellEquiv x o).val,s))) =
      ((PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (outsideVertex a),
       (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (xor o (SatWireExpansion.entryIndex s))) := by
  change ((outsideNumbering _ _).num a, (outerVertices.eval x).length+
    ((o.1.val*3+o.2.val)*8+(if s then 3 else 4))) = _
  rw [outsideNumbering_num,outerVertices_length]
  apply Prod.ext
  · rfl
  · cases s <;> simp [SatWireExpansion.entryIndex] <;> omega

theorem leavePair_eval (x : SatTy.denote) (a : Outside ((vsOf x).length +1) x.length)
    (o : Occurrence x.length) (s : Bool) :
    leavePair.eval (x,((outerEquiv x a).val,((cellEquiv x o).val,s))) =
      ((PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (xor o (SatWireExpansion.exitIndex s)),
       (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (outsideVertex a)) := by
  change ((outerVertices.eval x).length+
    ((o.1.val*3+o.2.val)*8+(if s then 0 else 7)),(outsideNumbering _ _).num a) = _
  rw [outsideNumbering_num,outerVertices_length]
  apply Prod.ext
  · cases s <;> simp [SatWireExpansion.exitIndex] <;> omega
  · rfl

theorem linkPair_eval (x : SatTy.denote) (o p : Occurrence x.length) (s t : Bool) :
    linkPair.eval (x,(((cellEquiv x o).val,s),((cellEquiv x p).val,t))) =
      ((PlanarSatCode.numbering ((vsOf x).length+1) x.length).num
        (xor o (SatWireExpansion.exitIndex s)),
       (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (xor p (SatWireExpansion.entryIndex t))) := by
  change ((outerVertices.eval x).length+((o.1.val*3+o.2.val)*8+(if s then 0 else 7)),
    (outerVertices.eval x).length+((p.1.val*3+p.2.val)*8+(if t then 3 else 4))) = _
  rw [outerVertices_length]
  apply Prod.ext
  · cases s <;> simp [SatWireExpansion.exitIndex] <;> omega
  · cases t <;> simp [SatWireExpansion.entryIndex] <;> omega

theorem enter_iff (x : SatTy.denote) (a : Outside ((vsOf x).length +1) x.length)
    (o : Occurrence x.length) (s : Bool) :
    XorWireCode.enter (assembly.eval x) (outerEquiv x a) (cellEquiv x o) s ↔
      SatWireExpansion.enter (finiteFormula x) a o s := by
  change ((outerEquiv x a).val,((cellEquiv x o).val,s)) ∈ entering.eval x ↔ _
  rw [mem_entering,enterPair_eval]
  have ha := (outerEquiv x a).isLt
  have ho := (cellEquiv x o).isLt
  change (outerEquiv x a).val < (outerVertices.eval x).length at ha
  change (cellEquiv x o).val < (cells.eval x).length at ho
  simp only [ha,ho,true_and,and_self]
  exact PlanarSatCode.mem_edgesCode x (outsideVertex a) (xor o (SatWireExpansion.entryIndex s))

theorem leave_iff (x : SatTy.denote) (a : Outside ((vsOf x).length +1) x.length)
    (o : Occurrence x.length) (s : Bool) :
    XorWireCode.leave (assembly.eval x) (cellEquiv x o) s (outerEquiv x a) ↔
      SatWireExpansion.leave (finiteFormula x) o s a := by
  change ((outerEquiv x a).val,((cellEquiv x o).val,s)) ∈ leaving.eval x ↔ _
  rw [mem_leaving,leavePair_eval]
  have ha := (outerEquiv x a).isLt
  have ho := (cellEquiv x o).isLt
  change (outerEquiv x a).val < (outerVertices.eval x).length at ha
  change (cellEquiv x o).val < (cells.eval x).length at ho
  simp only [ha,ho,true_and,and_self]
  exact PlanarSatCode.mem_edgesCode x (xor o (SatWireExpansion.exitIndex s)) (outsideVertex a)

theorem link_iff (x : SatTy.denote) (o p : Occurrence x.length) (s t : Bool) :
    XorWireCode.link (assembly.eval x) (cellEquiv x o) s (cellEquiv x p) t ↔
      SatWireExpansion.link (finiteFormula x) o s p t := by
  change (((cellEquiv x o).val,s),((cellEquiv x p).val,t)) ∈ linking.eval x ↔ _
  rw [mem_linking,linkPair_eval]
  have ho := (cellEquiv x o).isLt
  have hp := (cellEquiv x p).isLt
  change (cellEquiv x o).val < (cells.eval x).length at ho
  change (cellEquiv x p).val < (cells.eval x).length at hp
  simp only [ho,hp,true_and,and_self]
  exact PlanarSatCode.mem_edgesCode x (xor o (SatWireExpansion.exitIndex s))
    (xor p (SatWireExpansion.entryIndex t))

noncomputable def networkEquiv (x : SatTy.denote) (k : Nat) :
    SatWireExpansion.ExpandedVertex ((vsOf x).length+1) x.length k ≃
      (XorWireCode.Outer (assembly.eval x) ⊕
        (XorWireCode.Cell (assembly.eval x) × XorWire.Vertex k)) :=
  Equiv.sumCongr (outerEquiv x) (Equiv.prodCongr (cellEquiv x) (Equiv.refl _))

theorem network_arc_iff (x : SatTy.denote) (k : Nat)
    (u v : SatWireExpansion.ExpandedVertex ((vsOf x).length +1) x.length k) :
    SatWireExpansion.expanded (finiteFormula x) k u v ↔
      XorWire.network (XorWireCode.outside (assembly.eval x))
        (XorWireCode.enter (assembly.eval x)) (XorWireCode.leave (assembly.eval x))
        (XorWireCode.link (assembly.eval x)) k (networkEquiv x k u) (networkEquiv x k v) := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact (outside_iff x a b).symm
    | inr p =>
      rcases p with ⟨o,w⟩
      change (∃ b : Unit, ∃ s, SatWireExpansion.enter (finiteFormula x) a o s ∧
        w = XorWire.entry k s) ↔
        (∃ b : Unit, ∃ s, XorWireCode.enter (assembly.eval x) (outerEquiv x a)
          (cellEquiv x o) s ∧ w = XorWire.entry k s)
      exact exists_congr (fun _ => exists_congr (fun s =>
        and_congr (enter_iff x a o s).symm Iff.rfl))
  | inr p =>
    rcases p with ⟨o,w⟩
    cases v with
    | inl a =>
      change (∃ b : Unit, ∃ s, SatWireExpansion.leave (finiteFormula x) o s a ∧
        w = XorWire.exit k s) ↔
        (∃ b : Unit, ∃ s, XorWireCode.leave (assembly.eval x) (cellEquiv x o)
          s (outerEquiv x a) ∧ w = XorWire.exit k s)
      exact exists_congr (fun _ => exists_congr (fun s =>
        and_congr (leave_iff x a o s).symm Iff.rfl))
    | inr p =>
      rcases p with ⟨p,z⟩
      change ((o=p ∧ XorWire.Adj k w z) ∨ (o≠p ∧ ∃ b : Unit, ∃ s, ∃ c : Unit, ∃ t,
        SatWireExpansion.link (finiteFormula x) o s p t ∧
        w = XorWire.exit k s ∧ z = XorWire.entry k t)) ↔
        ((cellEquiv x o=cellEquiv x p ∧ XorWire.Adj k w z) ∨
        (cellEquiv x o≠cellEquiv x p ∧ ∃ b : Unit, ∃ s, ∃ c : Unit, ∃ t,
        XorWireCode.link (assembly.eval x) (cellEquiv x o) s (cellEquiv x p) t ∧
        w = XorWire.exit k s ∧ z = XorWire.entry k t))
      simp only [ne_eq,Equiv.apply_eq_iff_eq]
      apply or_congr Iff.rfl
      apply and_congr Iff.rfl
      exact exists_congr (fun _ => exists_congr (fun s =>
        exists_congr (fun _ => exists_congr (fun t =>
          and_congr (link_iff x o p s t).symm Iff.rfl))))

theorem assembly_source_correct (x : SatTy.denote) :
    Satisfiable (finiteFormula x) ↔ XorWireCode.SOURCE_HAMILTONIAN (assembly.eval x) := by
  change _ ↔ DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE
    ((XorWireCode.program (.const NatListTy [])).eval (assembly.eval x))
  rw [XorWireCode.program_interpretation]
  have hn : 0 < (assembly.eval x).1.1.length+(assembly.eval x).2.1.length := by
    change 0 < (outerVertices.eval x).length+(cells.eval x).length
    rw [outerVertices_length,cells_length]
    omega
  rw [and_iff_right hn]
  exact (SatWireExpansion.correct (finiteFormula x) 0).trans
    (PathCover.hamiltonian_relabel_iff _ _ (networkEquiv x 0) (network_arc_iff x 0))

/-- Reject malformed source syntax with a completely empty encoded network. -/
def code : Code SatTy InputTy :=
  .branch PlanarSatCode.syntaxGuard assembly
    (.const InputTy (([],([],0)),([],([],([],([],[]))))))

theorem code_correct (x : SatTy.denote) : Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
    XorWireCode.SOURCE_HAMILTONIAN (code.eval x) := by
  by_cases h : PlanarSatCode.syntaxGuard.eval x = true
  · rw [code,branch_eval_true _ _ h]
    obtain ⟨hw,hp⟩ := (PlanarSatCode.syntaxGuard_eval x).mp h
    exact (finiteFormula_correct x hw hp).symm.trans (assembly_source_correct x)
  · have hs : ¬ Concrete.MONOTONE_ONE_IN_THREE_SAT3 x := by
      intro hx
      obtain ⟨hp,hw,_⟩ := (Concrete.monotoneOneInThree3Sat_iff x).mp hx
      exact h ((PlanarSatCode.syntaxGuard_eval x).mpr ⟨hw,hp⟩)
    rw [code,branch_eval_false _ _ (Bool.eq_false_iff.mpr h)]
    change _ ↔ DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE
      ((XorWireCode.program (.const NatListTy [])).eval (([],([],0)),([],([],([],([],[]))))))
    rw [XorWireCode.program_interpretation]
    simp [hs]

def certified : CertifiedReduction Concrete.MONOTONE_ONE_IN_THREE_SAT3
    XorWireCode.SOURCE_HAMILTONIAN := ⟨code,code_correct⟩

/-- Concrete positive one-in-three SAT to the compiled stretched network. -/
def certifiedStretched : CertifiedReduction Concrete.MONOTONE_ONE_IN_THREE_SAT3
    DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE := certified.comp XorWireCode.certified

end GridHardness.XorWireCodeSat
