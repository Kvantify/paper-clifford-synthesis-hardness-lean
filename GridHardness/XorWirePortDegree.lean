/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireNetwork

/-!
# XOR Wire Port Degree

Characterize the incident edges at wire attachments and prove uniqueness of the ports
under the degree conditions of the replacement graph.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.XorWire.NetworkDegree

abbrev Endpoints (O C : Type*) := O ⊕ (C × Bool)
abbrev Vertices (O C : Type*) (n : Nat) := O ⊕ (C × XorWire.Vertex n)

variable {O C : Type*}

def Incoming (enter : O → C → Bool → Prop) (link : C → Bool → C → Bool → Prop)
    (c : C) (s : Bool) : Endpoints O C → Prop
  | .inl o => enter o c s
  | .inr (d,t) => d ≠ c ∧ link d t c s

def Outgoing (leave : C → Bool → O → Prop) (link : C → Bool → C → Bool → Prop)
    (c : C) (s : Bool) : Endpoints O C → Prop
  | .inl o => leave c s o
  | .inr (d,t) => c ≠ d ∧ link c s d t

def inEmbed (n : Nat) : Endpoints O C → Vertices O C n
  | .inl o => .inl o
  | .inr (c,s) => .inr (c,XorWire.exit n s)

def outEmbed (n : Nat) : Endpoints O C → Vertices O C n
  | .inl o => .inl o
  | .inr (c,s) => .inr (c,XorWire.entry n s)

theorem inEmbed_injective (n : Nat) : Function.Injective (inEmbed (O := O) (C := C) n) := by
  rintro (o | ⟨c,s⟩) (o' | ⟨c',s'⟩) h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · cases h
  · cases h
  · have hp := Sum.inr_injective h
    obtain ⟨rfl,hs⟩ := Prod.mk.inj hp
    have he := congrArg Prod.snd ((XorWire.output_injective n) (a₁ := ((),s)) (a₂ := ((),s')) hs)
    change s = s' at he
    subst s'
    rfl

theorem outEmbed_injective (n : Nat) : Function.Injective (outEmbed (O := O) (C := C) n) := by
  rintro (o | ⟨c,s⟩) (o' | ⟨c',s'⟩) h
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · cases h
  · cases h
  · have hp := Sum.inr_injective h
    obtain ⟨rfl,hs⟩ := Prod.mk.inj hp
    have he := congrArg Prod.snd ((XorWire.input_injective n) (a₁ := ((),s)) (a₂ := ((),s')) hs)
    change s = s' at he
    subst s'
    rfl

def PortsUnique (enter : O → C → Bool → Prop) (leave : C → Bool → O → Prop)
    (link : C → Bool → C → Bool → Prop) : Prop :=
  (∀ c s u v, Incoming enter link c s u → Incoming enter link c s v → u = v) ∧
  (∀ c s u v, Outgoing leave link c s u → Outgoing leave link c s v → u = v)

noncomputable def inDegree {V : Type*} [Fintype V] (D : V → V → Prop) (v : V) : Nat := by
  classical
  exact (Finset.univ.filter (fun u => D u v)).card

noncomputable def outDegree {V : Type*} [Fintype V] (D : V → V → Prop) (v : V) : Nat := by
  classical
  exact (Finset.univ.filter (fun u => D v u)).card

private theorem unique_of_card_le_two {A B : Type*} [Fintype A]
    (P : A → Prop) (Q : B → Prop) (f : B → A) (hf : Function.Injective f)
    (z : A) (hz : P z) (hn : ∀ b, Q b → f b ≠ z) (he : ∀ b, Q b → P (f b))
    (hb : by classical exact (Finset.univ.filter P).card ≤ 2) :
    ∀ a b, Q a → Q b → a = b := by
  classical
  intro a b ha hc
  by_contra hab
  have hfab : f a ≠ f b := fun h => hab (hf h)
  have hza : z ≠ f a := (hn a ha).symm
  have hzb : z ≠ f b := (hn b hc).symm
  have hs : ({z,f a,f b} : Finset A) ⊆ Finset.univ.filter P := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he a ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he b hc⟩
  have hk := Finset.card_le_card hs
  have hh : ({z,f a,f b} : Finset A).card = 3 := by simp [hza,hzb,hfab]
  omega

section
variable (outside : O → O → Prop) (enter : O → C → Bool → Prop)
variable (leave : C → Bool → O → Prop) (link : C → Bool → C → Bool → Prop)

 theorem incoming_edge (n : Nat) (c : C) (s : Bool) (v : Endpoints O C)
    (h : Incoming enter link c s v) :
    XorWire.network outside enter leave link n (inEmbed n v) (.inr (c,XorWire.entry n s)) := by
  cases v with
  | inl o => exact ⟨(),s,h,rfl⟩
  | inr p =>
    rcases p with ⟨d,t⟩
    exact Or.inr ⟨h.1,(),t,(),s,h.2,rfl,rfl⟩

theorem outgoing_edge (n : Nat) (c : C) (s : Bool) (v : Endpoints O C)
    (h : Outgoing leave link c s v) :
    XorWire.network outside enter leave link n (.inr (c,XorWire.exit n s)) (outEmbed n v) := by
  cases v with
  | inl o => exact ⟨(),s,h,rfl⟩
  | inr p =>
    rcases p with ⟨d,t⟩
    exact Or.inr ⟨h.1,(),s,(),t,h.2,rfl,rfl⟩

theorem incoming_ne_internal (n : Nat) (c : C) (s : Bool) (v : Endpoints O C)
    (h : Incoming enter link c s v) (w : XorWire.Vertex n) : inEmbed n v ≠ .inr (c,w) := by
  cases v with
  | inl o => intro he; cases he
  | inr p =>
    rcases p with ⟨d,t⟩
    intro he
    exact h.1 (congrArg Prod.fst (Sum.inr_injective he))

theorem outgoing_ne_internal (n : Nat) (c : C) (s : Bool) (v : Endpoints O C)
    (h : Outgoing leave link c s v) (w : XorWire.Vertex n) : outEmbed n v ≠ .inr (c,w) := by
  cases v with
  | inl o => intro he; cases he
  | inr p =>
    rcases p with ⟨d,t⟩
    intro he
    exact h.1 (congrArg Prod.fst (Sum.inr_injective he)).symm

/-- The length-zero degree bounds force each individual boundary port to
have at most one external neighbor. No extra non-collapse hypothesis is needed. -/
theorem portsUnique_of_zero_degree [Fintype O] [Fintype C]
    (hin : ∀ v, inDegree (XorWire.network outside enter leave link 0) v ≤ 2)
    (hout : ∀ v, outDegree (XorWire.network outside enter leave link 0) v ≤ 2) :
    PortsUnique enter leave link := by
  classical
  constructor
  · intro c s
    let z : Vertices O C 0 := .inr (c,(0,if s then 2 else 5))
    apply unique_of_card_le_two
      (fun w => XorWire.network outside enter leave link 0 w (.inr (c,XorWire.entry 0 s)))
      (Incoming enter link c s) (inEmbed 0) (inEmbed_injective 0) z
    · cases s
      · exact Or.inl ⟨rfl,Or.inl ⟨rfl,6,rfl⟩⟩
      · exact Or.inl ⟨rfl,Or.inl ⟨rfl,3,rfl⟩⟩
    · exact fun v hv => incoming_ne_internal enter link 0 c s v hv _
    · exact incoming_edge outside enter leave link 0 c s
    · exact hin _
  · intro c s
    let z : Vertices O C 0 := .inr (c,(0,if s then 1 else 6))
    apply unique_of_card_le_two
      (fun w => XorWire.network outside enter leave link 0 (.inr (c,XorWire.exit 0 s)) w)
      (Outgoing leave link c s) (outEmbed 0) (outEmbed_injective 0) z
    · cases s
      · exact Or.inl ⟨rfl,Or.inl ⟨rfl,9,rfl⟩⟩
      · exact Or.inl ⟨rfl,Or.inl ⟨rfl,0,rfl⟩⟩
    · exact fun v hv => outgoing_ne_internal leave link 0 c s v hv _
    · exact outgoing_edge outside enter leave link 0 c s
    · exact hout _

end
end GridHardness.XorWire.NetworkDegree
