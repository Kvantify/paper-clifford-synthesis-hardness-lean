/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedRouteLookupCode
public import GridHardness.DirectedPortSelectionCode
public import GridHardness.LatticeRouteEndpointCode

/-!
# Directed Incidence Record Code

Recover the local directed incidences by scanning explicit endpoint-keyed
route records. Both endpoint directions are computed from the route itself;
no precomputed incidence list is required.
-/

@[expose] public section

namespace GridHardness.DirectedIncidenceRecordCode
open CliffordComplexity GridProblems GridProblems.GridCode
open DirectedRouteLookupCode DirectedPortSelectionCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair RecordsTy .nat
abbrev LocalTy := Ty.pair .nat RecordTy

def endpoint (b : Bool) : Code LocalTy PortsTy :=
  let key := if b then .comp (.comp .snd .fst) .snd else .comp (.comp .snd .fst) .fst
  let hit :=  .comp (.pair .fst key) .natEq
  let port := .pair (.const .bool b)
    (.comp (.pair (.comp .snd .snd) (.const .bool b)) endpointDirectionCode)
  .branch hit (.comp port .listSingle) (.const PortsTy [])

def localCode : Code LocalTy PortsTy := Code.append (endpoint false) (endpoint true)

def code : Code InputTy PortsTy :=
  .comp (.pair .snd .fst) (.comp (.listMapEnv localCode) .listJoin)

def localPorts (q : Nat) (r : RecordTy.denote) : PortsTy.denote :=
  (if q=r.1.1 then [(false,endpointDirectionCode.eval (r.2,false))] else []) ++
  (if q=r.1.2 then [(true,endpointDirectionCode.eval (r.2,true))] else [])

theorem localCode_eval (q : Nat) (r : RecordTy.denote) :
    localCode.eval (q,r)=localPorts q r := by
  simp only [localCode, Code.append, Code.eval, endpoint, localPorts]
  simp only [Bool.false_eq_true, ite_false, ite_true, Code.eval, decide_eq_true_eq]

theorem code_eval (rs : RecordsTy.denote) (q : Nat) :
    code.eval (rs,q)=rs.flatMap (localPorts q) := by
  change ((rs.map (fun r => localCode.eval (q,r))).flatten)=_
  rw [List.flatMap_def]
  congr 1
  exact List.map_congr_left (fun r _ => localCode_eval q r)

theorem mem_localPorts (q : Nat) (r : RecordTy.denote) (p : PortTy.denote) :
    p∈localPorts q r ↔ ∃b:Bool,
      q=(if b then r.1.2 else r.1.1) ∧
      p=(b,endpointDirectionCode.eval (r.2,b)) := by
  cases p with | mk b d =>
    cases b <;> simp [localPorts, Bool.exists_bool, Prod.mk.injEq]

theorem mem_code (rs : RecordsTy.denote) (q : Nat) (p : PortTy.denote) :
    p∈code.eval (rs,q) ↔ ∃r∈rs,∃b:Bool,
      q=(if b then r.1.2 else r.1.1) ∧
      p=(b,endpointDirectionCode.eval (r.2,b)) := by
  rw [code_eval]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨r,hr,hp⟩
    exact ⟨r,hr,(mem_localPorts q r p).mp hp⟩
  · rintro ⟨r,hr,hp⟩
    exact ⟨r,hr,(mem_localPorts q r p).mpr hp⟩

end GridHardness.DirectedIncidenceRecordCode

namespace GridHardness.DirectedPortSelectionCode
open CliffordComplexity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- The fixed finite selector depends only on incidence membership, including
for raw encoded lists. Reordering or duplicating records has no effect. -/
theorem code_congr (rs ts : PortsTy.denote) (hm : ∀ p, p∈rs ↔ p ∈ts) :
    code.eval rs=code.eval ts := by
  have hc : ∀c:DirectedPortSelection.Port,(candidate c).eval rs=(candidate c).eval ts := by
    intro c
    apply Bool.eq_iff_iff.mpr
    change compatibleCode.eval (rs,encodePort c)=true ↔ compatibleCode.eval (ts,encodePort c)=true
    rw [compatibleCode, isNil_eval_true, isNil_eval_true]
    change (Code.filterEnv violates).eval (encodePort c,rs)=[] ↔
      (Code.filterEnv violates).eval (encodePort c,ts)=[]
    rw [filterEnv_eval,filterEnv_eval,List.filter_eq_nil_iff,List.filter_eq_nil_iff]
    constructor
    · intro h p hp
      exact h p ((hm p).mpr hp)
    · intro h p hp
      exact h p ((hm p).mp hp)
  simp only [code,Code.eval]
  rw [hc,hc,hc,hc,hc,hc,hc]

end GridHardness.DirectedPortSelectionCode
