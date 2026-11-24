/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrder
public import GridHardness.SatCrossingRetirementCatalogue

/-!
# SAT Clause Wire Lattice

Horizontal links from clause literal ports to the first crossing on
each occurrence wire, or to its retired XOR when there are no crossings.
The target is selected from the ascending request list. These are explicit
routes with vertex clearance; `SatClauseWireDrawing` identifies their endpoints
as arcs of the final graph.
-/

@[expose] public section

namespace GridHardness.SatClauseWireLattice
open CliffordSynthesis PlanarSatAssembly PermutationWireLayout
open CorrectedSatInterval SatCrossingRouting
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

variable {N n m : Nat} (p : Equiv.Perm (Fin N))

def firstRequest? (j : Fin N) : Option (Fin N) :=
  if hn : requests (permutationHeight p) j.val≠[] then
    some ⟨(requests (permutationHeight p) j.val).head hn,
      ((mem_requests _ _ _).mp (List.head_mem hn)).1.trans j.isLt⟩
  else none

theorem firstRequest_val (j : Fin N) :
    (firstRequest? p j).map Fin.val=(requests (permutationHeight p) j.val).head? := by
  unfold firstRequest?
  split
  · rename_i hn
    exact (List.head?_eq_some_head hn).symm
  · rename_i hn
    have h : requests (permutationHeight p) j.val=[] := by simpa using hn
    simp [h]

theorem firstRequest_sound (i j : Fin N) (hi : firstRequest? p j =some i) :
    Active p i j ∧ ∀ k, Active p k j → i≤k := by
  have hval := firstRequest_val p j
  rw [hi] at hval
  have hhead : (requests (permutationHeight p) j.val).head?=some i.val := hval.symm
  have hmem := List.mem_of_head? hhead
  refine ⟨(SatCrossingHorizontal.request_iff_active p i j).mp hmem,?_⟩
  intro k hk
  have hkm := (SatCrossingHorizontal.request_iff_active p k j).mpr hk
  have hpair : (requests (permutationHeight p) j.val).Pairwise (·≤·) :=
    (requests_increasing _ _).imp Nat.le_of_lt
  have hb := hpair.rel_head hkm
  rw [List.head_of_head?_eq_some hhead] at hb
  exact hb

theorem firstRequest_none (j : Fin N) :
    firstRequest? p j=none ↔ ∀ i, ¬Active p i j := by
  constructor
  · intro hn i hi
    have he := firstRequest_val p j
    rw [hn] at he
    have hnil := List.head?_eq_none_iff.mp he.symm
    have hm := (SatCrossingHorizontal.request_iff_active p i j).mpr hi
    rw [hnil] at hm
    contradiction
  · intro h
    cases he : firstRequest? p j with
    | none => rfl
    | some i => exact False.elim (h i (firstRequest_sound p i j he).1)

theorem firstRequest_correct (i j : Fin N) :
    firstRequest? p j=some i ↔ Active p i j ∧ ∀ k, Active p k j → i≤k := by
  constructor
  · exact firstRequest_sound p i j
  · rintro ⟨hi,hmin⟩
    cases he : firstRequest? p j with
    | none => exact False.elim ((firstRequest_none p j).mp he i hi)
    | some k =>
      obtain ⟨hk,hkmin⟩ := firstRequest_sound p k j he
      have hki : k=i := le_antisymm (hkmin i hi) (hmin k hk)
      simp [hki]

def finishX (j : Fin N) : Int :=
  match firstRequest? p j with
  | none => 0
  | some i => 512*low i-65

theorem finishX_bounds (j : Fin N) : 0≤finishX p j ∧ finishX p j≤512*N-65 := by
  have hj := j.isLt
  unfold finishX
  split
  · omega
  · rename_i i h
    have hi := low_bounds i
    omega

/-- `outgoing=false` runs east from the lower clause port; `true` runs
west to the upper clause port. -/
def height (j : Fin N) (outgoing : Bool) : Int :=
  512*high p j+if outgoing then -4 else 4

def segment (y : Int) (length : Nat) : List Point :=
  (List.range (length+1)).map (fun k : Nat => (-64+(k:Int),y))

def length (j : Fin N) : Nat := (finishX p j+64).toNat

def route (j : Fin N) (outgoing : Bool) : List Point :=
  if outgoing then (segment (height p j outgoing) (length p j)).reverse
  else segment (height p j outgoing) (length p j)

def clausePoint (j : Fin N) (b : Bool) : Point := (-64,height p j b)
def wirePoint (j : Fin N) (b : Bool) : Point := (finishX p j,height p j b)

theorem length_cast (j : Fin N) : (length p j:Int)=finishX p j+64 := by
  have h := finishX_bounds p j
  dsimp [length]
  omega

theorem segment_mem (y : Int) (l : Nat) (q : Point) :
    q∈segment y l ↔ q.2=y ∧ -64≤q.1 ∧ q.1≤-64+l := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    exact ⟨rfl,by omega,by omega⟩
  · rintro ⟨hy,hl,hu⟩
    refine List.mem_map.mpr ⟨(q.1+64).toNat,?_,?_⟩
    · simp only [List.mem_range]
      omega
    · apply Prod.ext <;> dsimp <;> omega

theorem segment_nodup (y : Int) (l : Nat) : (segment y l).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro a b he
  have hx := congrArg Prod.fst he
  dsimp at hx
  omega

theorem segment_chain (y : Int) (l : Nat) :
    (segment y l).IsChain UnitStep := by
  rw [segment,List.isChain_map,List.isChain_range]
  intro k _
  change IntegerGrid.manhattan _ _=1
  dsimp [IntegerGrid.manhattan]
  omega

theorem route_mem (j : Fin N) (b : Bool) (q : Point) :
    q∈route p j b ↔ q.2=height p j b ∧ -64≤q.1 ∧ q.1≤finishX p j := by
  have hl := length_cast p j
  cases b <;> simp only [route,Bool.false_eq_true,ite_false,ite_true,List.mem_reverse,segment_mem] <;>
    omega

theorem route_simple (j : Fin N) (b : Bool) :
    (route p j b).Nodup ∧ (route p j b).IsChain UnitStep := by
  cases b
  · exact ⟨segment_nodup _ _,segment_chain _ _⟩
  · refine ⟨List.nodup_reverse.mpr (segment_nodup _ _),?_⟩
    rw [route,ite_eq_left rfl,List.isChain_reverse]
    apply (segment_chain _ _).imp
    intro a b hab
    change IntegerGrid.manhattan _ _=1 at hab ⊢
    dsimp [IntegerGrid.manhattan] at hab ⊢
    omega

theorem route_endpoints (j : Fin N) (b : Bool) :
    (route p j b).head?=some (if b then wirePoint p j b else clausePoint p j b) ∧
    (route p j b).getLast?=some (if b then clausePoint p j b else wirePoint p j b) := by
  have hl := length_cast p j
  have hh (y : Int) (l : Nat) : (segment y l).head?=some (-64,y) := by
    simp [segment,List.range_succ_eq_map]
  have ht (y : Int) (l : Nat) : (segment y l).getLast?=some (-64+(l:Int),y) := by
    simp [segment,List.range_succ]
  cases b <;> simp [route,List.head?_reverse,List.getLast?_reverse,hh,ht,
    wirePoint,clausePoint,hl]

theorem route_length (j : Fin N) (b : Bool) : (route p j b).length=length p j+1 := by
  cases b <;> simp [route,segment]

theorem route_length_bound (j : Fin N) (b : Bool) :
    65≤(route p j b).length ∧ (route p j b).length≤512*N := by
  have hl := length_cast p j
  have hb := finishX_bounds p j
  rw [route_length]
  omega

theorem route_bounds (j : Fin N) (b : Bool) (q : Point) (hq : q ∈route p j b) :
    -64≤q.1 ∧ q.1≤512*N-65 ∧ 0≤q.2 ∧ q.2≤1024*N+516 := by
  have hr := (route_mem p j b q).mp hq
  have hx := finishX_bounds p j
  have hy := high_bounds p j
  cases b <;> dsimp [height] at hr <;> omega

theorem pairwise_separation (i j : Fin N) (a b : Bool) (hne : (i, a) ≠(j, b))
    (q r : Point) (hq : q ∈route p i a) (hr : r ∈route p j b) :
    8≤IntegerGrid.manhattan q r := by
  have hq' := (route_mem p i a q).mp hq
  have hr' := (route_mem p j b r).mp hr
  by_cases hij : i=j
  · subst j
    have hab : a≠b := fun h => hne (Prod.ext rfl h)
    cases a <;> cases b <;> simp_all [height,IntegerGrid.manhattan]
  · have hh : high p i≠high p j := fun h => hij (high_injective p h)
    cases a <;> cases b <;> dsimp [height,IntegerGrid.manhattan] at hq' hr' ⊢ <;> omega

theorem clause_endpoint (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    clausePoint (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b=
      SatClauseOrder.point o.1 (if b then clauseTop o.2 else clauseBottom o.2) := by
  have h := SatClauseOrder.literal_ports φ o
  cases b
  · exact h.1.symm
  · exact h.2.symm

theorem wire_endpoint_some (i j : Fin N) (h : firstRequest? p j =some i) (b : Bool) :
    wirePoint p j b=SatCrossingLattice.point p (i,j)
      (if b then XorLine.outputPort 4 (.inl false) else XorLine.inputPort 4 (.inl false)) := by
  have hp := SatCrossingLattice.main_port_coordinates p (i,j)
  cases b
  · simpa [wirePoint,finishX,h,height] using hp.2.2.1.symm
  · simpa [wirePoint,finishX,h,height,sub_eq_add_neg] using hp.2.2.2.symm

theorem wire_endpoint_none (j : Fin N) (h : firstRequest? p j =none) (b : Bool) :
    wirePoint p j b=SatCrossingWireVertices.retired p j (if b then 7 else 4) := by
  have hn : SatCrossingRetirement.Catalogue.lastRequest? p j=none :=
    (SatCrossingRetirement.Catalogue.lastRequest_none p j).mpr ((firstRequest_none p j).mp h)
  have hp (r : Fin 4) := SatCrossingRetirement.Placement.false_coordinates p none j
    (by intro i hi; cases hi) r
  cases b
  · simpa [wirePoint,finishX,h,height,SatCrossingWireVertices.retired,hn,
      SatCrossingRetirement.falseVertex,SatCrossingRetirement.Placement.left,
      SatCrossingRetirement.offset] using (hp 0).symm
  · simpa [wirePoint,finishX,h,height,SatCrossingWireVertices.retired,hn,
      SatCrossingRetirement.falseVertex,SatCrossingRetirement.Placement.left,
      SatCrossingRetirement.offset,sub_eq_add_neg] using (hp 3).symm

/-- The endpoint belongs to the existing simultaneous wire-vertex
placement, including the retained first cell in the nonempty case. -/
theorem wire_endpoint_is_vertex (j : Fin N) (b : Bool) :
    ∃ v : SatCrossingWireVertices.Vertex p, wirePoint p j b=SatCrossingWireVertices.point p v := by
  cases hf : firstRequest? p j with
  | none =>
    exact ⟨.inl (j,if b then 7 else 4),wire_endpoint_none p j hf b⟩
  | some i =>
    let c : WireCrossingSchedule.Cell p := ⟨(i,j),(firstRequest_sound p i j hf).1⟩
    let v : SatCrossingHorizontal.RetainedVertex :=
      ⟨if b then XorLine.outputPort 4 (.inl false) else XorLine.inputPort 4 (.inl false),
        by cases b <;> decide⟩
    exact ⟨.inr (c,v),wire_endpoint_some p i j hf b⟩

/-- Every active crossing box meets a clause link only at the selected
first crossing, at the intended false-side boundary port. -/
theorem active_box_intersection (j : Fin N) (b : Bool) (c : SatCrossingLattice.Cell N)
    (hc : Active p c.1 c.2) (q : Point) (hq : q ∈route p j b)
    (hb : SatCrossingLattice.InBox p c q) :
    firstRequest? p j=some c.1 ∧ c.2=j ∧ q=wirePoint p j b := by
  have hr := (route_mem p j b q).mp hq
  have hy : c.2=j := by
    apply high_injective p
    dsimp [SatCrossingLattice.InBox] at hb
    cases b <;> dsimp [height] at hr <;> omega
  rcases c with ⟨i,k⟩
  dsimp at hy
  subst k
  cases hf : firstRequest? p j with
  | none => exact False.elim ((firstRequest_none p j).mp hf i hc)
  | some a =>
    have ha := firstRequest_sound p a j hf
    have hle := ha.2 i hc
    have hx : q.1≤512*low a-65 := by simpa [finishX,hf] using hr.2.2
    dsimp [SatCrossingLattice.InBox] at hb
    have hai : a=i := by
      apply Fin.ext
      dsimp [low] at hx hb
      exact Nat.le_antisymm hle (by omega)
    subst a
    refine ⟨rfl,rfl,?_⟩
    apply Prod.ext
    · simpa only [wirePoint,finishX,hf] using le_antisymm hx hb.1
    · exact hr.1

theorem active_edge_intersection (j : Fin N) (b : Bool) (c : SatCrossingLattice.Cell N)
    (hc : Active p c.1 c.2) (e : Fin 66) (q : Point)
    (hq : q ∈route p j b) (he : q ∈SatCrossingLattice.route p c e) :
    firstRequest? p j=some c.1 ∧ c.2=j ∧ q=wirePoint p j b ∧
      ((if b then XorLine.outputPort 4 (.inl false) else XorLine.inputPort 4 (.inl false))=
          (XorLine.Lattice.edge e).1 ∨
       (if b then XorLine.outputPort 4 (.inl false) else XorLine.inputPort 4 (.inl false))=
          (XorLine.Lattice.edge e).2) := by
  obtain ⟨hf,hj,hq'⟩ := active_box_intersection p j b c hc q hq
    (SatCrossingLattice.route_in_box p c e q he)
  refine ⟨hf,hj,hq',?_⟩
  rcases c with ⟨i,k⟩
  dsimp at hj
  subst k
  rw [hq',wire_endpoint_some p i j hf b] at he
  exact (SatCrossingLattice.route_vertex_clear p (i,j) e _).mp he

/-- On the clause side, the route meets every clause box only at its
own literal vertex. This includes the two extreme backbone ports. -/
theorem clause_box_intersection (φ : Formula n m) (o : Occurrence m) (b : Bool)
    (c : Fin m) (q : Point)
    (hq : q ∈route (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b)
    (hc : SatClauseOrder.InBox c q) :
    c=o.1 ∧ q=SatClauseOrder.point o.1 (if b then clauseTop o.2 else clauseBottom o.2) := by
  have hr := (route_mem (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b q).mp hq
  have hb := SatClauseOrder.coordinates_bounded c q hc
  have hp : q=clausePoint (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b := by
    apply Prod.ext
    · dsimp [clausePoint]
      omega
    · exact hr.1
  rw [clause_endpoint] at hp
  refine ⟨?_,hp⟩
  by_contra hn
  have hs := SatClauseOrder.boxes_separated c o.1 hn q q hc
    (hp.symm ▸ SatClauseOrder.point_in_box o.1 (if b then clauseTop o.2 else clauseBottom o.2))
  simp [IntegerGrid.manhattan] at hs

theorem clause_internal_intersection (φ : Formula n m) (o : Occurrence m) (b : Bool)
    (c : Fin m) (e : Fin 14) (q : Point)
    (hq : q ∈route (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o) b)
    (he : q ∈SatClauseOrder.route c e) :
    c=o.1 ∧ q=SatClauseOrder.point o.1 (if b then clauseTop o.2 else clauseBottom o.2) ∧
      ((if b then clauseTop o.2 else clauseBottom o.2)=(PlanarSatClause.Lattice.edge e).1 ∨
       (if b then clauseTop o.2 else clauseBottom o.2)=(PlanarSatClause.Lattice.edge e).2) := by
  obtain ⟨hc,hp⟩ := clause_box_intersection φ o b c q hq (SatClauseOrder.route_in_box c e q he)
  subst c
  refine ⟨rfl,hp,?_⟩
  rw [hp] at he
  exact (SatClausePlacement.route_vertex_clear (Fin.rev o.1) e _).mp he

end GridHardness.SatClauseWireLattice
