/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteDrawing
public import GridHardness.DirectedIncidenceSaturation
public import GridHardness.DirectedPortSelection

/-!
# SAT Bipartite Ports

At each vertex of the SAT drawing, at least one of the incoming and
outgoing sides has at most one incidence. A fixed finite search over incidence
records selects a cardinal port used exactly by that side; an empty side
receives an unused port. `SatDirectedIncidenceCode` computes the incidences
from directed vertex and arc records.
-/

@[expose] public section

namespace GridHardness.SatBipartitePorts
open CliffordComplexity PlanarSatAssembly SatCompleteDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Tagged (x : SatTy.denote) (v : Vertex x) :=
  DirectedIncidenceSaturation.Incidence (SatClauseOrder.graph (finiteFormula x)).adj v

def tagged (x : SatTy.denote) (v : Vertex x) : Incidence x v → Tagged x v := by
  rintro ⟨⟨a,b⟩,h⟩
  cases b
  · exact .inr ⟨target x a, by
      have hs : source x a = v := h
      rw [← hs]
      exact a.property⟩
  · exact .inl ⟨source x a, by
      have ht : target x a = v := h
      rw [← ht]
      exact a.property⟩

def untagged (x : SatTy.denote) (v : Vertex x) : Tagged x v → Incidence x v
  | .inl u => ⟨(⟨(u.val,v),u.property⟩,true),rfl⟩
  | .inr u => ⟨(⟨(v,u.val),u.property⟩,false),rfl⟩

theorem tagged_injective (x : SatTy.denote) (v : Vertex x) :
    Function.Injective (tagged x v) := by
  apply Function.LeftInverse.injective (f := tagged x v) (g := untagged x v)
  rintro ⟨⟨a,b⟩,h⟩
  cases b <;> apply Subtype.ext <;> apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext h.symm rfl
  · rfl
  · apply Subtype.ext
    exact Prod.ext rfl h.symm
  · rfl

theorem incidence_card_le (x : SatTy.denote) (v : Vertex x) :
    Nat.card (Incidence x v) ≤ 3 := by
  have hi := Nat.card_le_card_of_injective (tagged x v) (tagged_injective x v)
  have hd := (DirectedIncidenceSaturation.permutation_bounds (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) v).2.2
  have ht : Nat.card (Tagged x v) ≤ 3 := by
    simpa only [Tagged, DirectedIncidenceSaturation.incidence_card, SatClauseOrder.graph] using hd
  exact hi.trans ht

/-- One of the two directed sides has at most one incidence. -/
theorem exists_singleton_side (x : SatTy.denote) (v : Vertex x) :
    ∃ b : Bool, ∀ i j : Incidence x v,
      i.val.2=b → j.val.2=b → i=j := by
  classical
  have hd := (DirectedIncidenceSaturation.permutation_bounds (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) v).2.2
  let D := (SatClauseOrder.graph (finiteFormula x)).adj
  by_cases hin : Nat.card {u : Vertex x // D u v} ≤ 1
  · let : Fintype {u : Vertex x // D u v} := Fintype.ofFinite _
    let : Subsingleton {u : Vertex x // D u v} :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        simpa only [Nat.card_eq_fintype_card] using hin)
    refine ⟨true, ?_⟩
    rintro ⟨⟨a,b⟩,ha⟩ ⟨⟨c,d⟩,hc⟩ hb hd
    dsimp at hb hd
    subst b
    subst d
    have ha' : target x a = v := ha
    have hc' : target x c = v := hc
    have haa : D (source x a) v := by rw [← ha']; exact a.property
    have hcc : D (source x c) v := by rw [← hc']; exact c.property
    have he : source x a = source x c :=
      congrArg Subtype.val (Subsingleton.elim (⟨source x a,haa⟩ : {u // D u v})
        ⟨source x c,hcc⟩)
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (Prod.ext he (ha'.trans hc'.symm))
    · rfl
  · have hout : Nat.card {u : Vertex x // D v u} ≤ 1 := by
      change Nat.card {u : Vertex x // D u v} + Nat.card {u : Vertex x // D v u} ≤ 3 at hd
      omega
    let : Fintype {u : Vertex x // D v u} := Fintype.ofFinite _
    let : Subsingleton {u : Vertex x // D v u} :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        simpa only [Nat.card_eq_fintype_card] using hout)
    refine ⟨false, ?_⟩
    rintro ⟨⟨a,b⟩,ha⟩ ⟨⟨c,d⟩,hc⟩ hb hd
    dsimp at hb hd
    subst b
    subst d
    have ha' : source x a = v := ha
    have hc' : source x c = v := hc
    have haa : D v (target x a) := by rw [← ha']; exact a.property
    have hcc : D v (target x c) := by rw [← hc']; exact c.property
    have he : target x a = target x c :=
      congrArg Subtype.val (Subsingleton.elim (⟨target x a,haa⟩ : {u // D v u})
        ⟨target x c,hcc⟩)
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (Prod.ext (ha'.trans hc'.symm) he)
    · rfl

/-- The chosen side is exactly the set of incidences using the chosen
cardinal direction. Here `true` means incoming, and `false` outgoing. -/
structure Choice (x : SatTy.denote) (v : Vertex x) where
  incoming : Bool
  direction : Fin 4
  direction_iff : ∀ i : Incidence x v,
    SatCompleteDrawing.direction x i.val.1 i.val.2 = direction ↔ i.val.2=incoming

/-- Four ports suffice because the total degree is at most three, and
the two directed sides cannot both have at least two incidences. -/
theorem choice_exists (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : Nonempty (Choice x v) := by
  classical
  obtain ⟨b,hb⟩ := exists_singleton_side x v
  by_cases hocc : ∃ i : Incidence x v, i.val.2=b
  · obtain ⟨i,hi⟩ := hocc
    refine ⟨⟨b,SatCompleteDrawing.direction x i.val.1 i.val.2,?_⟩⟩
    intro j
    constructor
    · intro he
      have hji := incident_directions_injective x hw v he
      simpa only [hji] using hi
    · intro hj
      have hji := hb j i hj hi
      rw [hji]
  · have hmissing : ∃ d : Fin 4, ∀ i : Incidence x v,
        SatCompleteDrawing.direction x i.val.1 i.val.2 ≠ d := by
      by_contra hh
      push Not at hh
      have hs : Function.Surjective
          (fun i : Incidence x v => SatCompleteDrawing.direction x i.val.1 i.val.2) := hh
      have hc := Nat.card_le_card_of_surjective _ hs
      have hi := incidence_card_le x v
      simp only [Nat.card_fin] at hc
      omega
    obtain ⟨d,hd⟩ := hmissing
    refine ⟨⟨b,d,?_⟩⟩
    intro i
    exact ⟨fun h => False.elim (hd i h), fun h => False.elim (hocc ⟨i,h⟩)⟩

/-- Explicit incidence records for the local finite selector. Their
enumeration is immaterial: the selector depends only on list membership. -/
noncomputable def incidencePorts (x : SatTy.denote) (v : Vertex x) :
    List DirectedPortSelection.Port := by
  classical
  letI := Fintype.ofFinite (Incidence x v)
  exact Finset.univ.toList.map (fun i : Incidence x v =>
    (i.val.2,SatCompleteDrawing.direction x i.val.1 i.val.2))

theorem mem_incidencePorts (x : SatTy.denote) (v : Vertex x)
    (p : DirectedPortSelection.Port) :
    p∈incidencePorts x v ↔ ∃i:Incidence x v,
      (i.val.2,SatCompleteDrawing.direction x i.val.1 i.val.2)=p := by
  classical
  simp [incidencePorts]

theorem incidencePorts_length (x : SatTy.denote) (v : Vertex x) :
    (incidencePorts x v).length=Nat.card (Incidence x v) := by
  classical
  letI := Fintype.ofFinite (Incidence x v)
  simp [incidencePorts, Nat.card_eq_fintype_card]

theorem incidencePorts_length_le (x : SatTy.denote) (v : Vertex x) :
    (incidencePorts x v).length≤3 := by
  rw [incidencePorts_length]
  exact incidence_card_le x v

theorem incidencePorts_exists (x : SatTy.denote) (hw : ∀ c∈x, c.length =3)
    (v : Vertex x) : ∃p:DirectedPortSelection.Port,∀r∈incidencePorts x v,
      r.2=p.2 ↔ r.1=p.1 := by
  obtain ⟨c⟩ := choice_exists x hw v
  refine ⟨(c.incoming,c.direction),?_⟩
  intro r hr
  obtain ⟨i,rfl⟩ := (mem_incidencePorts x v r).mp hr
  exact c.direction_iff i

/-- Canonical finite selection from the valid port candidates.
The existence theorem is used only to prove the selected port's invariant. -/
noncomputable def choose (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : Choice x v :=
  let c := DirectedPortSelection.choose (incidencePorts x v)
  { incoming := c.1
    direction := c.2
    direction_iff := fun i => DirectedPortSelection.choose_valid (incidencePorts x v)
      (incidencePorts_exists x hw v)
      (i.val.2,SatCompleteDrawing.direction x i.val.1 i.val.2)
      ((mem_incidencePorts x v _).mpr ⟨i,rfl⟩) }

theorem choose_eq_selector (x : SatTy.denote) (hw : ∀ c∈x, c.length =3)
    (v : Vertex x) :
    ((choose x hw v).incoming,(choose x hw v).direction)=
      DirectedPortSelection.choose (incidencePorts x v) := rfl

theorem singleton_side (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i j : Incidence x v)
    (hi : i.val.2 =(choose x hw v).incoming)
    (hj : j.val.2 =(choose x hw v).incoming) : i=j := by
  apply incident_directions_injective x hw v
  exact ((choose x hw v).direction_iff i).mpr hi |>.trans
    (((choose x hw v).direction_iff j).mpr hj).symm

end GridHardness.SatBipartitePorts
