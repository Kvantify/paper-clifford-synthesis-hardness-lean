/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariablePlacement
public import GridHardness.SatVariableWireClearance
public import GridHardness.SatGlobalVertexPlacement
public import GridHardness.CorrectedSatIntervalTrueEdges

/-!
# SAT Variable Chain Drawing

Draw the actual occurrence-chain links of each nonempty variable block.
The endpoints keep their original SAT vertex names through an arbitrary
permutation sweep. This family omits the direct variable branches, which
are drawn separately, and makes no assertion of a complete global drawing.
-/

@[expose] public section

namespace GridHardness.SatVariableChainDrawing
open CliffordSynthesis PlanarSatAssembly SatVariableOrder SatVariableLattice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
/-- Variable-body vertices and the two true ports of occurrence XORs.
The Boolean on a wire port is `false` for input and `true` for output. -/
abbrev Vertex (n m : Nat) := (Fin n × Bool) ⊕ (Occurrence m × Bool)

def port (output : Bool) : Fin 8 := if output then 0 else 3

def original {n m : Nat} : Vertex n m → PlanarSatAssembly.Vertex n m
  | .inl (v,b) => var v b
  | .inr (o,b) => PlanarSatAssembly.xor o (port b)

variable {n m : Nat}

theorem port_injective : Function.Injective port := by decide +kernel

theorem original_injective : Function.Injective (original (n := n) (m := m)) := by
  intro u v he
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      exact congrArg Sum.inl (Sum.inl.inj (Sum.inr.inj he))
    | inr v => cases he
  | inr u =>
    cases v with
    | inl v => cases he
    | inr v =>
      have h := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj he))
      have ho : u.1=v.1 := congrArg (fun z : Occurrence m × Fin 8 => z.1) h
      have hb : u.2=v.2 := port_injective (congrArg (fun z : Occurrence m × Fin 8 => z.2) h)
      exact congrArg Sum.inr (Prod.ext ho hb)

inductive Edge (φ : Formula n m) where
  | entry (v : Fin n) (positive : 0<count φ v)
  | between (v : Fin n) (k l : Fin (count φ v)) (consecutive : l.val=k.val+1)
  | exit (v : Fin n) (positive : 0<count φ v)

def owner {φ : Formula n m} : Edge φ → Fin n
  | .entry v _ => v
  | .between v _ _ _ => v
  | .exit v _ => v

def endpoints {φ : Formula n m} : Edge φ → Vertex n m × Vertex n m
  | .entry v h => (.inl (v,false),.inr (indexedOccurrence φ v ⟨0,h⟩,false))
  | .between v k l _ => (.inr (indexedOccurrence φ v k,true),.inr (indexedOccurrence φ v l,false))
  | .exit v h => (.inr (indexedOccurrence φ v ⟨count φ v-1,by omega⟩,true),.inl (v,true))

def sourceEndpoints {φ : Formula n m} (e : Edge φ) :
    PlanarSatAssembly.Vertex n m × PlanarSatAssembly.Vertex n m :=
  (original (endpoints e).1,original (endpoints e).2)

def chainIndex {φ : Formula n m} : Edge φ → Nat
  | .entry _ _ => 0
  | .between _ k _ _ => k.val+1
  | .exit v _ => count φ v

theorem chainIndex_lt {φ : Formula n m} (e : Edge φ) :
    chainIndex e < (variableChain φ (owner e)).length := by
  cases e <;> simp only [chainIndex,owner,variableChain_length]
  · omega
  · change _ < count φ _+1
    omega
  · change count φ _ < count φ _+1
    omega

/-- Each route index corresponds to its exact position in the source zip,
including the first and final links. -/
theorem source_get {φ : Formula n m} (e : Edge φ) :
    (variableChain φ (owner e))[chainIndex e]'(chainIndex_lt e)=sourceEndpoints e := by
  cases e with
  | entry v h =>
    simp only [owner,chainIndex,variableChain,List.getElem_zip,List.getElem_cons_zero,
      sourceEndpoints,endpoints,original,port,Bool.false_eq_true,ite_false]
    rw [List.getElem_append_left (by simpa only [List.length_map,count] using h)]
    simp only [List.getElem_map,indexedOccurrence]
  | between v k l h =>
    simp only [owner,chainIndex,variableChain,List.getElem_zip,List.getElem_cons_succ,
      sourceEndpoints,endpoints,original,port,ite_true,Bool.false_eq_true,ite_false]
    rw [List.getElem_append_left (by simp only [List.length_map]; change k.val+1<count φ v; omega)]
    simp only [List.getElem_map]
    have he : (occurrencesOf φ v)[k.val+1]'(by change _<count φ v; omega)=indexedOccurrence φ v l := by
      simp only [indexedOccurrence,h]
    rw [he]
    rfl
  | exit v h =>
    simp only [owner,chainIndex,sourceEndpoints,endpoints,original,port,
      ite_true,variableChain,List.getElem_zip]
    rw [List.getElem_cons]
    rw [List.getElem_append_right (by simp [count])]
    have he : occurrencesOf φ v≠[] := by
      intro he
      simp [count,he] at h
    simp [indexedOccurrence,count,he]

theorem source_mem {φ : Formula n m} (e : Edge φ) :
    sourceEndpoints e∈variableChain φ (owner e) :=
  List.mem_iff_getElem.mpr ⟨chainIndex e,chainIndex_lt e,source_get e⟩

/-- Every source occurrence-chain link is indexed by this family, except
the empty chain's copy of the already drawn direct variable branch. -/
theorem source_complete (φ : Formula n m) (v : Fin n)
    (u w : PlanarSatAssembly.Vertex n m) (h : (u, w) ∈variableChain φ v) :
    (count φ v=0 ∧ u=var v false ∧ w=var v true) ∨
      ∃ e : Edge φ, owner e=v ∧ sourceEndpoints e=(u,w) := by
  by_cases hc : count φ v=0
  · left
    have he : occurrencesOf φ v=[] := List.length_eq_zero_iff.mp hc
    simpa [variableChain,he] using And.intro hc h
  · have hp : 0<count φ v := by omega
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    have hi' : i<count φ v+1 := by simpa only [variableChain_length,count] using hi
    by_cases hz : i=0
    · subst i
      exact Or.inr ⟨.entry v hp,rfl,(source_get (.entry v hp)).symm.trans he⟩
    · by_cases hl : i=count φ v
      · subst i
        exact Or.inr ⟨.exit v hp,rfl,(source_get (.exit v hp)).symm.trans he⟩
      · let k : Fin (count φ v) := ⟨i-1,by omega⟩
        let l : Fin (count φ v) := ⟨i,by omega⟩
        have hkl : l.val=k.val+1 := by dsimp [k,l]; omega
        have hg := source_get (.between v k l hkl)
        have hind : chainIndex (.between v k l hkl)=i := by dsimp [chainIndex,k]; omega
        have hg' : (variableChain φ v)[i]'hi=sourceEndpoints (.between v k l hkl) := by
          simpa only [hind,owner] using hg
        exact Or.inr ⟨.between v k l hkl,rfl,hg'.symm.trans he⟩

def point (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) : Vertex n m → Point
  | .inl (v,b) => SatVariablePlacement.point φ v b
  | .inr (o,b) => SatCrossingWireVertices.retired p (SatWireLayout.variableRank φ o) (port b)

def route {φ : Formula n m} : Edge φ → List Point
  | .entry v _ => entryRoute (3*m) (SatVariableOrder.prefix φ v)
  | .between v k _ _ =>
    betweenRoute (3*m) (SatWireLayout.variableRank φ (indexedOccurrence φ v k)).val
  | .exit v _ => exitRoute (3*m) (SatVariableOrder.prefix φ v+count φ v)

theorem retired_input (p : Equiv.Perm (Fin (3 *m))) (i : Fin (3 *m)) :
    SatCrossingWireVertices.retired p i 3=input (3*m) i.val := by
  have h := SatCrossingRetirement.Placement.true_coordinates p
    (SatCrossingRetirement.Catalogue.lastRequest? p i) i
    (SatCrossingRetirement.Catalogue.last_before p i) (3 : Fin 4)
  simpa [SatCrossingWireVertices.retired,SatCrossingRetirement.trueVertex,
    SatCrossingRetirement.offset,PermutationWireLayout.low,
    input,wireX,sub_eq_add_neg] using h

theorem retired_output (p : Equiv.Perm (Fin (3 *m))) (i : Fin (3 *m)) :
    SatCrossingWireVertices.retired p i 0=output (3*m) i.val := by
  have h := SatCrossingRetirement.Placement.true_coordinates p
    (SatCrossingRetirement.Catalogue.lastRequest? p i) i
    (SatCrossingRetirement.Catalogue.last_before p i) (0 : Fin 4)
  simpa [SatCrossingWireVertices.retired,SatCrossingRetirement.trueVertex,
    SatCrossingRetirement.offset,PermutationWireLayout.low,
    output,wireX] using h

theorem route_endpoints (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge φ) :
    (route e).head?=some (point φ p (endpoints e).1) ∧
    (route e).getLast?=some (point φ p (endpoints e).2) := by
  cases e with
  | entry v h =>
    have hr := entryRoute_endpoints (3*m) (SatVariableOrder.prefix φ v)
    simpa only [route,endpoints,point,SatVariablePlacement.point,port,
      Bool.false_eq_true,ite_false,retired_input,first_rank] using hr
  | between v k l h =>
    have hr := betweenRoute_certificate (3*m)
      (SatWireLayout.variableRank φ (indexedOccurrence φ v k)).val
    have he := consecutive_ranks φ v k l h
    simpa only [route,endpoints,point,port,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      retired_output,retired_input,he] using And.intro hr.1 hr.2.1
  | exit v h =>
    have hb : 0<SatVariableOrder.prefix φ v+count φ v := by omega
    have hr := exitRoute_endpoints (3*m) (SatVariableOrder.prefix φ v+count φ v) hb
    have he := last_rank φ v h
    have he' : (SatWireLayout.variableRank φ
        (indexedOccurrence φ v ⟨count φ v-1,by omega⟩)).val=
        SatVariableOrder.prefix φ v+count φ v-1 := by omega
    simpa only [route,endpoints,point,port,Bool.true_eq,ite_true,retired_output,he',
      SatVariablePlacement.point,ite_eq_right (by omega : ¬count φ v=0)] using hr

theorem route_simple {φ : Formula n m} (e : Edge φ) :
    (route e).Nodup ∧ (route e).IsChain UnitStep := by
  cases e with
  | entry v h => exact entryRoute_simple _ _
  | between v k l h =>
    have hr := betweenRoute_certificate (3*m)
      (SatWireLayout.variableRank φ (indexedOccurrence φ v k)).val
    exact ⟨hr.2.2.1,hr.2.2.2.1⟩
  | exit v h => exact exitRoute_simple _ _

theorem route_length {φ : Formula n m} (e : Edge φ) :
    2≤(route e).length ∧ (route e).length≤505 := by
  cases e with
  | entry v h => simp only [route,entryRoute_length]; omega
  | between v k l h =>
    have hr := betweenRoute_certificate (3*m)
      (SatWireLayout.variableRank φ (indexedOccurrence φ v k)).val
    change 2≤(betweenRoute _ _).length ∧ (betweenRoute _ _).length≤505
    omega
  | exit v h => simp only [route,exitRoute_length]; omega

theorem route_bounds {φ : Formula n m} (e : Edge φ) (q : Point) (hq : q ∈route e) :
    wireX (3*m)≤q.1 ∧ q.1≤wireX (3*m)+64 ∧
      0≤q.2 ∧ q.2≤512*(3*m:Int)+64 := by
  cases e with
  | entry v h =>
    have hb := prefix_add_count_le φ v
    have hr := entryRoute_bounds (3*m) (SatVariableOrder.prefix φ v) q hq
    dsimp [entryY] at hr
    omega
  | between v k l h =>
    have hr := (SatCrossingRouting.rising_mem _ _ _ q).mp hq
    have he := consecutive_ranks φ v k l h
    have hl := (SatWireLayout.variableRank φ (indexedOccurrence φ v l)).isLt
    omega
  | exit v h =>
    have hb := prefix_add_count_le φ v
    have hr := exitRoute_bounds (3*m) (SatVariableOrder.prefix φ v+count φ v) q hq
    dsimp [exitY] at hr
    omega

noncomputable def vertex (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v : Vertex n m) : (CorrectedSatInterval.PermutationGraph.graph φ p).Vertex :=
  CorrectedSatInterval.PermutationGraph.liftOriginal φ p (original v)

theorem vertex_injective (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Function.Injective (vertex φ p) :=
  (CorrectedSatInterval.PermutationGraph.liftOriginal_injective φ p).comp original_injective

theorem point_injective (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (p : Equiv.Perm (Fin (3 *m))) : Function.Injective (point φ p) := by
  intro u v he
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      exact congrArg Sum.inl (SatVariablePlacement.point_injective φ hφ he)
    | inr v =>
      have hx := congrArg Prod.fst he
      have hu := SatVariablePlacement.point_x φ u.1 u.2
      have hv := SatCrossingWireVertices.retired_bounds p (SatWireLayout.variableRank φ v.1) (port v.2)
      change (SatVariablePlacement.point φ u.1 u.2).1=
        (SatCrossingWireVertices.retired p (SatWireLayout.variableRank φ v.1) (port v.2)).1 at hx
      dsimp [wireX] at hu
      omega
  | inr u =>
    cases v with
    | inl v =>
      have hx := congrArg Prod.fst he
      have hv := SatVariablePlacement.point_x φ v.1 v.2
      have hu := SatCrossingWireVertices.retired_bounds p (SatWireLayout.variableRank φ u.1) (port u.2)
      change (SatCrossingWireVertices.retired p (SatWireLayout.variableRank φ u.1) (port u.2)).1=
        (SatVariablePlacement.point φ v.1 v.2).1 at hx
      dsimp [wireX] at hv
      omega
    | inr v =>
      have h : (SatWireLayout.variableRank φ u.1,port u.2)=
          (SatWireLayout.variableRank φ v.1,port v.2) :=
        SatCrossingWireVertices.retired_injective p
          (a₁ := (SatWireLayout.variableRank φ u.1,port u.2))
          (a₂ := (SatWireLayout.variableRank φ v.1,port v.2)) he
      have ho : u.1=v.1 := (SatWireLayout.variableRank φ).injective (congrArg Prod.fst h)
      have hb : u.2=v.2 := port_injective (congrArg Prod.snd h)
      exact congrArg Sum.inr (Prod.ext ho hb)

theorem same_point_iff_same_vertex (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (p : Equiv.Perm (Fin (3 *m))) (u v : Vertex n m) :
    point φ p u=point φ p v ↔ vertex φ p u=vertex φ p v :=
  ⟨fun h => congrArg _ (point_injective φ hφ p h),
    fun h => congrArg _ (vertex_injective φ p h)⟩

theorem edge_is_arc (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge φ) :
    (CorrectedSatInterval.PermutationGraph.graph φ p).adj
      (vertex φ p (endpoints e).1) (vertex φ p (endpoints e).2) :=
  CorrectedSatInterval.TrueEdges.variable_chain_edge φ p (owner e) _ _ (source_mem e)

/-- The routes touch the wire envelope only at their designated true-port
endpoints. Their variable-body endpoints lie outside that envelope. -/
theorem wire_intersection (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (e : Edge φ) (q : Point) (hq : q ∈route e) (hw : SatClauseWireSeparation.WirePoint p q) :
    q=point φ p (endpoints e).1 ∨ q=point φ p (endpoints e).2 := by
  cases e with
  | entry v h =>
    have hb := prefix_add_count_le φ v
    have hr := SatVariableWireClearance.entry_intersection p (SatVariableOrder.prefix φ v)
      (by omega) q hq hw
    right
    simpa only [endpoints,point,port,Bool.false_eq_true,ite_false,retired_input,first_rank] using hr
  | between v k l h =>
    have hr := SatVariableWireClearance.between_intersection p
      (SatWireLayout.variableRank φ (indexedOccurrence φ v k)).val q hq hw
    have he := consecutive_ranks φ v k l h
    simpa only [endpoints,point,port,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      retired_output,retired_input,he] using hr
  | exit v h =>
    have hb := prefix_add_count_le φ v
    have hr := SatVariableWireClearance.exit_intersection p
      (SatVariableOrder.prefix φ v+count φ v) (by omega) hb q hq hw
    have he := last_rank φ v h
    have he' : (SatWireLayout.variableRank φ
        (indexedOccurrence φ v ⟨count φ v-1,by omega⟩)).val=
        SatVariableOrder.prefix φ v+count φ v-1 := by omega
    left
    simpa only [endpoints,point,port,Bool.true_eq,ite_true,retired_output,he'] using hr

/-- Chain ports use the same coordinates as every other final-graph vertex. -/
theorem actualPoint_vertex (φ : Formula n m) (v : Vertex n m) :
    SatGlobalVertexPlacement.actualPoint φ
      (vertex φ (SatClauseOrder.permutation φ) v)=
        point φ (SatClauseOrder.permutation φ) v := by
  rcases v with ⟨w,b⟩ | ⟨o,b⟩
  · exact SatGlobalVertexPlacement.actualPoint_variable φ w b
  · change SatGlobalVertexPlacement.actualPoint φ
      (CorrectedSatInterval.PermutationGraph.liftOriginal φ
        (SatClauseOrder.permutation φ) (PlanarSatAssembly.xor o (port b)))=_
    rw [← CorrectedSatInterval.PermutationWirePlacement.vertex_occurrence,
      SatGlobalVertexPlacement.actualPoint_wire]
    rfl

theorem actual_route_endpoints (φ : Formula n m) (e : Edge φ) :
    (route e).head?=some (SatGlobalVertexPlacement.actualPoint φ
      (vertex φ (SatClauseOrder.permutation φ) (endpoints e).1)) ∧
    (route e).getLast?=some (SatGlobalVertexPlacement.actualPoint φ
      (vertex φ (SatClauseOrder.permutation φ) (endpoints e).2)) := by
  rw [actualPoint_vertex,actualPoint_vertex]
  exact route_endpoints φ (SatClauseOrder.permutation φ) e

end GridHardness.SatVariableChainDrawing
