/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRouting

/-!
# SAT Variable Lattice

Routes along the right boundary for a consecutive block of occurrence
wires. A nonempty variable block has an entry before its first wire and an
exit after its last wire. The direct branch is 64 steps to the right of the
wire boundary. These formulas depend on positions, not variable labels.
-/

@[expose] public section

namespace GridHardness.SatVariableLattice
open CliffordSynthesis SatCrossingRouting
set_option autoImplicit false

abbrev Point := Int × Int
abbrev UnitStep := XorLine.Lattice.UnitStep

def wireX (N : Nat) : Int := 512*((N:Int)+1)+65
def entryY (a : Nat) : Int := 512*(a:Int)+128
def exitY (b : Nat) : Int := 512*(b:Int)+64
def entry (N a : Nat) : Point := (wireX N+64,entryY a)
def exit (N b : Nat) : Point := (wireX N+64,exitY b)
def input (N i : Nat) : Point := (wireX N,512*((i:Int)+1)-4)
def output (N i : Nat) : Point := (wireX N,512*((i:Int)+1)+4)

def entryPoint (N a k : Nat) : Point :=
  if k≤64 then (wireX N+64-k,entryY a)
  else (wireX N,entryY a+((k:Int)-64))

def entryRoute (N a : Nat) : List Point := (List.range 445).map (entryPoint N a)

def exitPoint (N b k : Nat) : Point :=
  if k≤60 then (wireX N,exitY b-60+k)
  else (wireX N+((k:Int)-60),exitY b)

def exitRoute (N b : Nat) : List Point := (List.range 125).map (exitPoint N b)

def directRoute (N a b : Nat) : List Point :=
  rising (wireX N+64) (entryY a) (exitY b-entryY a).toNat

def betweenRoute (N i : Nat) : List Point :=
  rising (wireX N) (512*((i:Int)+1)+4) 504

def backboneRoute (N b : Nat) : List Point :=
  rising (wireX N+64) (exitY b) 64

/-- The extra unused variable at the end of the variable list. -/
def emptyExit (N a : Nat) : Point := (wireX N+64,entryY a+64)
def emptyRoute (N a : Nat) : List Point := rising (wireX N+64) (entryY a) 64

theorem entryPoint_injective (N a : Nat) : Function.Injective (entryPoint N a) := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [entryPoint] at hx hy
  split_ifs at hx hy <;> dsimp at hx hy <;> omega

theorem exitPoint_injective (N b : Nat) : Function.Injective (exitPoint N b) := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [exitPoint] at hx hy
  split_ifs at hx hy <;> dsimp at hx hy <;> omega

theorem entryPoint_step (N a k : Nat) : UnitStep (entryPoint N a k) (entryPoint N a (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [entryPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem exitPoint_step (N b k : Nat) : UnitStep (exitPoint N b k) (exitPoint N b (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [exitPoint,IntegerGrid.manhattan]
  split_ifs <;> dsimp <;> omega

theorem entryRoute_simple (N a : Nat) :
    (entryRoute N a).Nodup ∧ (entryRoute N a).IsChain UnitStep := by
  refine ⟨List.Nodup.map (entryPoint_injective N a) List.nodup_range,?_⟩
  rw [entryRoute,List.isChain_map,List.isChain_range]
  exact fun k _ => entryPoint_step N a k

theorem exitRoute_simple (N b : Nat) :
    (exitRoute N b).Nodup ∧ (exitRoute N b).IsChain UnitStep := by
  refine ⟨List.Nodup.map (exitPoint_injective N b) List.nodup_range,?_⟩
  rw [exitRoute,List.isChain_map,List.isChain_range]
  exact fun k _ => exitPoint_step N b k

theorem entryRoute_endpoints (N a : Nat) :
    (entryRoute N a).head?=some (entry N a) ∧
    (entryRoute N a).getLast?=some (input N a) := by
  constructor
  · simp [entryRoute,List.head?_range,entryPoint,entry]
  · simp [entryRoute,List.getLast?_range,entryPoint,input,entryY]
    omega

theorem exitRoute_endpoints (N b : Nat) (hb : 0 <b) :
    (exitRoute N b).head?=some (output N (b-1)) ∧
    (exitRoute N b).getLast?=some (exit N b) := by
  constructor
  · simp [exitRoute,List.head?_range,exitPoint,output,exitY]
    omega
  · simp [exitRoute,List.getLast?_range,exitPoint,exit]

theorem entryRoute_length (N a : Nat) : (entryRoute N a).length=445 := by
  simp [entryRoute]

theorem exitRoute_length (N b : Nat) : (exitRoute N b).length=125 := by
  simp [exitRoute]

theorem entryRoute_mem (N a : Nat) (q : Point) :
    q∈entryRoute N a ↔
      (q.2=entryY a ∧ wireX N≤q.1 ∧ q.1≤wireX N+64) ∨
      (q.1=wireX N ∧ entryY a≤q.2 ∧ q.2≤512*((a:Int)+1)-4) := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    dsimp [entryPoint]
    split_ifs with h
    · left; dsimp; omega
    · right; dsimp [entryY]; omega
  · intro h
    apply List.mem_map.mpr
    rcases h with ⟨hy,hx,hx'⟩ | ⟨hx,hy,hy'⟩
    · let k := (wireX N+64-q.1).toNat
      have hk : (k:Int)=wireX N+64-q.1 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      rw [entryPoint,ite_eq_left (by omega)]
      apply Prod.ext <;> dsimp <;> omega
    · let k := (q.2-entryY a+64).toNat
      have hk : (k:Int)=q.2-entryY a+64 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; dsimp [entryY] at *; omega,?_⟩
      dsimp [entryPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega

theorem exitRoute_mem (N b : Nat) (q : Point) :
    q∈exitRoute N b ↔
      (q.1=wireX N ∧ exitY b-60≤q.2 ∧ q.2≤exitY b) ∨
      (q.2=exitY b ∧ wireX N≤q.1 ∧ q.1≤wireX N+64) := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    dsimp [exitPoint]
    split_ifs with h
    · left; dsimp; omega
    · right; dsimp; omega
  · intro h
    apply List.mem_map.mpr
    rcases h with ⟨hx,hy,hy'⟩ | ⟨hy,hx,hx'⟩
    · let k := (q.2-exitY b+60).toNat
      have hk : (k:Int)=q.2-exitY b+60 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      rw [exitPoint,ite_eq_left (by omega)]
      apply Prod.ext <;> dsimp <;> omega
    · let k := (q.1-wireX N+60).toNat
      have hk : (k:Int)=q.1-wireX N+60 := by dsimp [k]; omega
      refine ⟨k,by simp only [List.mem_range]; omega,?_⟩
      dsimp [exitPoint]
      split_ifs <;> apply Prod.ext <;> dsimp <;> omega

theorem directRoute_mem (N a b : Nat) (hab : a <b) (q : Point) :
    q∈directRoute N a b ↔ q.1=wireX N+64 ∧ entryY a≤q.2 ∧ q.2≤exitY b := by
  have hy : entryY a≤exitY b := by dsimp [entryY,exitY]; omega
  rw [directRoute,rising_mem]
  omega

theorem directRoute_certificate (N a b : Nat) (hab : a <b) :
    (directRoute N a b).head?=some (entry N a) ∧
    (directRoute N a b).getLast?=some (exit N b) ∧
    (directRoute N a b).Nodup ∧ (directRoute N a b).IsChain UnitStep ∧
    (directRoute N a b).length=512*(b-a)-63 := by
  have hy : entryY a≤exitY b := by dsimp [entryY,exitY]; omega
  refine ⟨rising_head _ _ _,?_,rising_nodup _ _ _,rising_chain _ _ _,?_⟩
  · rw [directRoute,rising_last]
    apply congrArg some
    apply Prod.ext
    · rfl
    · dsimp [exit]
      omega
  · rw [directRoute,rising_length]
    dsimp [entryY,exitY]
    omega

theorem betweenRoute_certificate (N i : Nat) :
    (betweenRoute N i).head?=some (output N i) ∧
    (betweenRoute N i).getLast?=some (input N (i+1)) ∧
    (betweenRoute N i).Nodup ∧ (betweenRoute N i).IsChain UnitStep ∧
    (betweenRoute N i).length=505 := by
  refine ⟨rising_head _ _ _,?_,rising_nodup _ _ _,rising_chain _ _ _,rising_length _ _ _⟩
  rw [betweenRoute,rising_last]
  apply congrArg some
  apply Prod.ext <;> dsimp [input]
  all_goals omega

theorem backboneRoute_certificate (N b : Nat) :
    (backboneRoute N b).head?=some (exit N b) ∧
    (backboneRoute N b).getLast?=some (entry N b) ∧
    (backboneRoute N b).Nodup ∧ (backboneRoute N b).IsChain UnitStep ∧
    (backboneRoute N b).length=65 := by
  refine ⟨rising_head _ _ _,?_,rising_nodup _ _ _,rising_chain _ _ _,rising_length _ _ _⟩
  rw [backboneRoute,rising_last]
  apply congrArg some
  apply Prod.ext <;> dsimp [entry,exitY,entryY]
  all_goals omega

theorem emptyRoute_certificate (N a : Nat) :
    (emptyRoute N a).head?=some (entry N a) ∧
    (emptyRoute N a).getLast?=some (emptyExit N a) ∧
    (emptyRoute N a).Nodup ∧ (emptyRoute N a).IsChain UnitStep ∧
    (emptyRoute N a).length=65 :=
  ⟨rising_head _ _ _,rising_last _ _ _,rising_nodup _ _ _,rising_chain _ _ _,rising_length _ _ _⟩

/-- Every entry and exit stays in the exterior strip of width 64. -/
theorem entryRoute_bounds (N a : Nat) (q : Point) (hq : q ∈entryRoute N a) :
    wireX N≤q.1 ∧ q.1≤wireX N+64 ∧ entryY a≤q.2 ∧ q.2≤512*((a:Int)+1)-4 := by
  have h := (entryRoute_mem N a q).mp hq
  dsimp [entryY] at h ⊢
  rcases h with h | h <;> omega

theorem exitRoute_bounds (N b : Nat) (q : Point) (hq : q ∈exitRoute N b) :
    wireX N≤q.1 ∧ q.1≤wireX N+64 ∧ exitY b-60≤q.2 ∧ q.2≤exitY b := by
  have h := (exitRoute_mem N b q).mp hq
  rcases h with h | h <;> omega

theorem entry_direct_intersection (N a b : Nat) (hab : a <b) (q : Point)
    (he : q ∈entryRoute N a) (hd : q ∈directRoute N a b) : q=entry N a := by
  have he' := (entryRoute_mem N a q).mp he
  have hd' := (directRoute_mem N a b hab q).mp hd
  rcases he' with h | h <;> apply Prod.ext <;> dsimp [entry] <;> omega

theorem exit_direct_intersection (N a b : Nat) (hab : a <b) (q : Point)
    (he : q ∈exitRoute N b) (hd : q ∈directRoute N a b) : q=exit N b := by
  have he' := (exitRoute_mem N b q).mp he
  have hd' := (directRoute_mem N a b hab q).mp hd
  rcases he' with h | h <;> apply Prod.ext <;> dsimp [exit] <;> omega

theorem entry_exit_disjoint (N a b : Nat) (_hab : a <b) :
    (entryRoute N a).Disjoint (exitRoute N b) := by
  apply List.disjoint_left.mpr
  intro q he hx
  have he' := entryRoute_bounds N a q he
  have hx' := exitRoute_bounds N b q hx
  dsimp [entryY,exitY] at he' hx'
  omega

end GridHardness.SatVariableLattice
