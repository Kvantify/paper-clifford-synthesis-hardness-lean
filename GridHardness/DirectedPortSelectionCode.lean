/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedPortSelection
public import GridHardness.GridFrameCode

/-!
# Directed Port Selection Code

The canonical port selector as an actual polynomial Code program.
The finite search is fixed syntax; its tests scan only the supplied explicit
incidence records.
-/

@[expose] public section

namespace GridHardness.DirectedPortSelectionCode
open CliffordComplexity GridPointCode DirectedPortSelection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev PortTy := Ty.pair .bool .nat
abbrev PortsTy := Ty.list PortTy

def encodePort (p : Port) : PortTy.denote := (p.1,p.2.val)

/-- An incidence violates the candidate precisely when direction equality
and directed-side equality have different truth values. -/
def violates : Code (.pair PortTy PortTy) .bool :=
  .comp (.pair
    (.comp (.pair (.comp .snd .snd) (.comp .fst .snd)) .natEq)
    (.comp (.comp (.pair (.comp .snd .fst) (.comp .fst .fst)) GridFrameCode.xor) .boolNot))
    GridFrameCode.xor

theorem violates_eval (c r : Port) :
    violates.eval (encodePort c,encodePort r) =
      decide (¬(r.2=c.2 ↔ r.1=c.1)) := by
  rcases c with ⟨b,d⟩
  rcases r with ⟨a,e⟩
  cases a <;> cases b <;> by_cases h : e=d <;>
    simp [violates, encodePort, Code.eval, GridFrameCode.xor, h, Fin.ext_iff]
  all_goals exact decide_eq_false (fun he => h (Fin.ext he))

def compatibleCode : Code (.pair PortsTy PortTy) .bool :=
  Code.isNil (.comp (.pair .snd .fst) (Code.filterEnv violates))

theorem compatibleCode_eval (rs : List Port) (c : Port) :
    compatibleCode.eval (rs.map encodePort,encodePort c) = compatible rs c := by
  apply Bool.eq_iff_iff.mpr
  rw [compatibleCode, isNil_eval_true]
  change (Code.filterEnv violates).eval (encodePort c,rs.map encodePort)=[] ↔ _
  rw [filterEnv_eval, List.filter_eq_nil_iff, compatible_iff]
  simp only [List.mem_map]
  constructor
  · intro h r hr
    have hh := h (encodePort r) ⟨r,hr,rfl⟩
    rw [violates_eval] at hh
    simpa using hh
  · intro h p hp
    obtain ⟨r,hr,rfl⟩ := hp
    rw [violates_eval]
    simpa using h r hr

def candidate (c : Port) : Code PortsTy .bool :=
  .comp (.pair .id (.const PortTy (encodePort c))) compatibleCode

theorem candidate_eval (c : Port) (rs : List Port) :
    (candidate c).eval (rs.map encodePort)=compatible rs c := compatibleCode_eval rs c

def code : Code PortsTy PortTy :=
  .branch (candidate (true,0)) (.const PortTy (encodePort (true,0)))
    (.branch (candidate (true,1)) (.const PortTy (encodePort (true,1)))
      (.branch (candidate (true,2)) (.const PortTy (encodePort (true,2)))
        (.branch (candidate (true,3)) (.const PortTy (encodePort (true,3)))
          (.branch (candidate (false,0)) (.const PortTy (encodePort (false,0)))
            (.branch (candidate (false,1)) (.const PortTy (encodePort (false,1)))
              (.branch (candidate (false,2)) (.const PortTy (encodePort (false,2)))
                (.const PortTy (encodePort (false,3)))))))))

/-- Exact evaluation of the canonical selector on any incidence list. -/
theorem code_eval (rs : List Port) : code.eval (rs.map encodePort)=encodePort (choose rs) := by
  simp only [code, Code.eval]
  rw [candidate_eval, candidate_eval, candidate_eval, candidate_eval,
    candidate_eval, candidate_eval, candidate_eval]
  unfold choose select
  split_ifs <;> rfl

/-- Every output port has the required incidence property whenever such
a port exists. Existence is proved for the actual SAT graph separately. -/
theorem code_valid (rs : List Port)
    (hex : ∃ c:Port, ∀r∈rs, r.2 =c.2 ↔ r.1 =c.1) :
    ∀r∈rs,r.2.val=(code.eval (rs.map encodePort)).2 ↔
      r.1=(code.eval (rs.map encodePort)).1 := by
  rw [code_eval]
  intro r hr
  simpa only [encodePort, Fin.ext_iff] using choose_valid rs hex r hr

end GridHardness.DirectedPortSelectionCode
