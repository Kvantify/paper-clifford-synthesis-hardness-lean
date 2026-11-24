/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableLattice
public import GridHardness.SatClauseWireSeparation

/-!
# SAT Exterior Lattice

Exterior routes joining the sentinel, variable and clause parts.
The long forward link passes to the right and above the wire rectangle;
the return link passes below the lowest clause on the left. These are
explicit lattice paths, with clearance proved from the existing geometry.
-/

@[expose] public section

namespace GridHardness.SatExteriorLattice
open CliffordSynthesis SatVariableLattice
set_option autoImplicit false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

def sentinel (N : Nat) : Fin 3 → Point :=
  ![(-128,0),(-128,-64),(wireX N+64,-64)]

def downPoint (k : Nat) : Point := (-128,-(k:Int))
def down : List Point := (List.range 65).map downPoint
def bottomPoint (k : Nat) : Point := (-128+(k:Int),-64)
def bottom (N : Nat) : List Point := (List.range (512*N+770)).map bottomPoint
def firstVariable (N : Nat) : List Point := SatCrossingRouting.rising (wireX N+64) (-64) 192

def top (N : Nat) : Int := 1024*(N:Int)+640
def clauseEntry (N : Nat) : Point := (-64,1024*(N:Int)+516)
def clauseExit (N : Nat) : Point := (-64,512*(N:Int)+1020)

def forwardPoint (N k : Nat) : Point :=
  if k≤64 then (wireX N+64+k,512*(N:Int)+192)
  else if k≤512*N+512 then (wireX N+128,512*(N:Int)+128+k)
  else if k≤1024*N+1281 then (1024*(N:Int)+1217-k,top N)
  else (-64,2048*(N:Int)+1921-k)

def forward (N : Nat) : List Point :=
  (List.range (1024*N+1406)).map (forwardPoint N)

def returnPoint (N k : Nat) : Point :=
  if k≤512*N+1020 then (-64,512*(N:Int)+1020-k)
  else (512*(N:Int)+956-k,0)

def returning (N : Nat) : List Point :=
  (List.range (512*N+1085)).map (returnPoint N)

theorem down_simple : down.Nodup ∧ down.IsChain UnitStep := by
  constructor
  · apply List.Nodup.map _ List.nodup_range
    intro k l h
    have hy := congrArg Prod.snd h
    dsimp [downPoint] at hy
    omega
  · rw [down,List.isChain_map,List.isChain_range]
    intro k _
    change IntegerGrid.manhattan _ _=1
    dsimp [downPoint,IntegerGrid.manhattan]
    omega

theorem bottom_simple (N : Nat) : (bottom N).Nodup ∧ (bottom N).IsChain UnitStep := by
  constructor
  · apply List.Nodup.map _ List.nodup_range
    intro k l h
    have hx := congrArg Prod.fst h
    dsimp [bottomPoint] at hx
    omega
  · rw [bottom,List.isChain_map,List.isChain_range]
    intro k _
    change IntegerGrid.manhattan _ _=1
    dsimp [bottomPoint,IntegerGrid.manhattan]
    omega

theorem sentinel_endpoints (N : Nat) :
    down.head?=some (sentinel N 0) ∧ down.getLast?=some (sentinel N 1) ∧
    (bottom N).head?=some (sentinel N 1) ∧ (bottom N).getLast?=some (sentinel N 2) := by
  simp [down,bottom,downPoint,bottomPoint,sentinel,wireX,List.head?_range,List.getLast?_range]
  omega

theorem firstVariable_certificate (N : Nat) :
    (firstVariable N).head?=some (sentinel N 2) ∧
    (firstVariable N).getLast?=some (entry N 0) ∧
    (firstVariable N).Nodup ∧ (firstVariable N).IsChain UnitStep ∧
    (firstVariable N).length=193 := by
  refine ⟨SatCrossingRouting.rising_head _ _ _,?_,SatCrossingRouting.rising_nodup _ _ _,
    SatCrossingRouting.rising_chain _ _ _,SatCrossingRouting.rising_length _ _ _⟩
  rw [firstVariable,SatCrossingRouting.rising_last]
  rfl

theorem forwardPoint_injective (N : Nat) : Function.Injective (forwardPoint N) := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [forwardPoint] at hx hy
  split_ifs at hx hy <;> dsimp [wireX,top] at hx hy <;> omega

theorem forwardPoint_step (N k : Nat) :
    UnitStep (forwardPoint N k) (forwardPoint N (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [forwardPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp [wireX,top] <;> omega

theorem forward_simple (N : Nat) :
    (forward N).Nodup ∧ (forward N).IsChain UnitStep := by
  refine ⟨List.Nodup.map (forwardPoint_injective N) List.nodup_range,?_⟩
  rw [forward,List.isChain_map,List.isChain_range]
  exact fun k _ => forwardPoint_step N k

theorem forward_endpoints (N : Nat) :
    (forward N).head?=some (emptyExit N N) ∧
    (forward N).getLast?=some (clauseEntry N) := by
  constructor
  · simp [forward,List.head?_range,forwardPoint,emptyExit,entryY]
    omega
  · simp [forward,List.getLast?_range,forwardPoint,clauseEntry]
    split_ifs <;> simp_all [wireX] <;> omega

theorem forward_length (N : Nat) : (forward N).length=1024*N+1406 := by
  simp [forward]

theorem forward_support (N : Nat) (q : Point) (hq : q ∈forward N) :
    (q.2=512*(N:Int)+192 ∧ wireX N+64≤q.1 ∧ q.1≤wireX N+128) ∨
    (q.1=wireX N+128 ∧ 512*(N:Int)+192≤q.2 ∧ q.2≤top N) ∨
    (q.2=top N ∧ -64≤q.1 ∧ q.1≤wireX N+128) ∨
    (q.1=-64 ∧ 1024*(N:Int)+516≤q.2 ∧ q.2≤top N) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [forwardPoint]
  split_ifs with h₁ h₂ h₃
  · left; dsimp [wireX]; omega
  · right; left; dsimp [top]; omega
  · right; right; left; dsimp [wireX,top]; omega
  · right; right; right; dsimp [top]; omega

theorem returnPoint_injective (N : Nat) : Function.Injective (returnPoint N) := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [returnPoint] at hx hy
  split_ifs at hx hy <;> dsimp at hx hy <;> omega

theorem returnPoint_step (N k : Nat) :
    UnitStep (returnPoint N k) (returnPoint N (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [returnPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem returning_simple (N : Nat) :
    (returning N).Nodup ∧ (returning N).IsChain UnitStep := by
  refine ⟨List.Nodup.map (returnPoint_injective N) List.nodup_range,?_⟩
  rw [returning,List.isChain_map,List.isChain_range]
  exact fun k _ => returnPoint_step N k

theorem returning_endpoints (N : Nat) :
    (returning N).head?=some (clauseExit N) ∧
    (returning N).getLast?=some (sentinel N 0) := by
  constructor
  · simp [returning,List.head?_range,returnPoint,clauseExit]
  · simp [returning,List.getLast?_range,returnPoint,sentinel]

theorem returning_length (N : Nat) : (returning N).length=512*N+1085 := by
  simp [returning]

theorem returning_support (N : Nat) (q : Point) (hq : q ∈returning N) :
    (q.1=-64 ∧ 0≤q.2 ∧ q.2≤512*(N:Int)+1020) ∨
    (q.2=0 ∧ -128≤q.1 ∧ q.1≤-64) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [returnPoint]
  split_ifs
  · left; dsimp; omega
  · right; dsimp; omega

theorem forward_wire_separation {N : Nat} (p : Equiv.Perm (Fin N)) (q r : Point)
    (hq : q ∈forward N) (hr : SatClauseWireSeparation.WirePoint p r) :
    64≤IntegerGrid.manhattan q r := by
  have hb := SatClauseWireSeparation.wire_bounds p r hr
  have hs := forward_support N q hq
  dsimp [IntegerGrid.manhattan,wireX,top] at hs ⊢
  rcases hs with hs | hs | hs | hs <;> omega

theorem returning_wire_separation {N : Nat} (p : Equiv.Perm (Fin N)) (q r : Point)
    (hq : q ∈returning N) (hr : SatClauseWireSeparation.WirePoint p r) :
    64≤IntegerGrid.manhattan q r := by
  have hb := SatClauseWireSeparation.wire_bounds p r hr
  have hs := returning_support N q hq
  dsimp [IntegerGrid.manhattan]
  rcases hs with hs | hs <;> omega

theorem forward_clause_intersection {m : Nat} (c : Fin m) (q : Point)
    (hq : q ∈forward (3 *m)) (hc : SatClauseOrder.InBox c q) :
    c.val=0 ∧ q=SatClauseOrder.point c 8 := by
  have hs := forward_support (3*m) q hq
  change -104≤q.1 ∧ q.1≤-64 ∧ SatClauseOrder.base c-4≤q.2 ∧
    q.2≤SatClauseOrder.base c+1028 at hc
  rw [SatClauseOrder.base_eq] at hc
  have hcb := c.isLt
  dsimp [wireX,top] at hs
  have hv : c.val=0 ∧ q.1=-64 ∧ q.2=3072*(m:Int)+516 := by
    rcases hs with hs | hs | hs | hs <;> omega
  refine ⟨hv.1,?_⟩
  rw [(SatClauseOrder.backbone_ports c).1,SatClauseOrder.base_eq]
  apply Prod.ext <;> dsimp <;> omega

theorem returning_clause_intersection {m : Nat} (c : Fin m) (q : Point)
    (hq : q ∈returning (3 *m)) (hc : SatClauseOrder.InBox c q) :
    c.val+1=m ∧ q=SatClauseOrder.point c 1 := by
  have hs := returning_support (3*m) q hq
  change -104≤q.1 ∧ q.1≤-64 ∧ SatClauseOrder.base c-4≤q.2 ∧
    q.2≤SatClauseOrder.base c+1028 at hc
  rw [SatClauseOrder.base_eq] at hc
  have hcb := c.isLt
  have hv : c.val+1=m ∧ q.1=-64 ∧ q.2=1536*(m:Int)+1020 := by
    rcases hs with hs | hs <;> omega
  refine ⟨hv.1,?_⟩
  rw [(SatClauseOrder.backbone_ports c).2,SatClauseOrder.base_eq]
  apply Prod.ext <;> dsimp <;> omega

theorem forward_returning_disjoint (m : Nat) (hm : 0 <m) :
    (forward (3*m)).Disjoint (returning (3*m)) := by
  apply List.disjoint_left.mpr
  intro q hf hr
  have hf' := forward_support (3*m) q hf
  have hr' := returning_support (3*m) q hr
  dsimp [wireX,top] at hf'
  rcases hf' with hf' | hf' | hf' | hf' <;> rcases hr' with hr' | hr' <;> omega

theorem forward_bounds (N : Nat) (q : Point) (hq : q ∈forward N) :
    -64≤q.1 ∧ q.1≤wireX N+128 ∧ 0≤q.2 ∧ q.2≤top N := by
  have hs := forward_support N q hq
  dsimp [wireX,top] at hs ⊢
  rcases hs with hs | hs | hs | hs <;> omega

theorem returning_bounds (N : Nat) (q : Point) (hq : q ∈returning N) :
    -128≤q.1 ∧ q.1≤-64 ∧ 0≤q.2 ∧ q.2≤512*(N:Int)+1020 := by
  have hs := returning_support N q hq
  rcases hs with hs | hs <;> omega

/-- With no clauses the extra variable closes straight back to the
sentinel, along the outside of the same rectangle. No fictitious clause
vertex is added. -/
def closingPoint (k : Nat) : Point :=
  if k≤1921 then forwardPoint 0 k else (1857-(k:Int),0)

def closing : List Point := (List.range 1986).map closingPoint

theorem closingPoint_injective : Function.Injective closingPoint := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [closingPoint,forwardPoint] at hx hy
  split_ifs at hx hy <;> dsimp [wireX,top] at hx hy <;> omega

theorem closingPoint_step (k : Nat) : UnitStep (closingPoint k) (closingPoint (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [closingPoint,forwardPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp [wireX,top] <;> omega

theorem closing_simple : closing.Nodup ∧ closing.IsChain UnitStep := by
  refine ⟨List.Nodup.map closingPoint_injective List.nodup_range,?_⟩
  rw [closing,List.isChain_map,List.isChain_range]
  exact fun k _ => closingPoint_step k

theorem closing_endpoints :
    closing.head?=some (emptyExit 0 0) ∧ closing.getLast?=some (sentinel 0 0) := by
  simp [closing,List.head?_range,List.getLast?_range,closingPoint,forwardPoint,
    emptyExit,entryY,wireX,sentinel]

theorem closing_length : closing.length=1986 := by simp [closing]

theorem closing_support (q : Point) (hq : q ∈closing) :
    (q.2=192 ∧ 641≤q.1 ∧ q.1≤705) ∨
    (q.1=705 ∧ 192≤q.2 ∧ q.2≤640) ∨
    (q.2=640 ∧ -64≤q.1 ∧ q.1≤705) ∨
    (q.1=-64 ∧ 0≤q.2 ∧ q.2≤640) ∨
    (q.2=0 ∧ -128≤q.1 ∧ q.1≤-64) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [closingPoint,forwardPoint]
  split_ifs with h₁ h₂ h₃ h₄
  · left; dsimp [wireX]; omega
  · right; left; dsimp [wireX]; omega
  · right; right; left; dsimp [top]; omega
  · right; right; right; left; dsimp; omega
  · right; right; right; right; dsimp; omega

end GridHardness.SatExteriorLattice
