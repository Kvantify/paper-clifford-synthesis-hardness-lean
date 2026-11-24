/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedScaledLayout

/-!
# Directed Port Selection

A canonical choice of the directed side occupying the outer endpoint
of a four-vertex replacement gadget. The fixed search order is incoming
east/north/west/south, then outgoing east/north/west/south.
-/

@[expose] public section

namespace GridHardness.DirectedPortSelection
set_option autoImplicit false

abbrev Port := Bool × Fin 4

/-- Fixed finite search, with its final candidate as the total default. -/
def select (good : Port → Bool) : Port :=
  if good (true,0) then (true,0) else
  if good (true,1) then (true,1) else
  if good (true,2) then (true,2) else
  if good (true,3) then (true,3) else
  if good (false,0) then (false,0) else
  if good (false,1) then (false,1) else
  if good (false,2) then (false,2) else (false,3)

theorem select_valid (good : Port → Bool) (hex : ∃ c, good c =true) :
    good (select good)=true := by
  unfold select
  split_ifs with h0 h1 h2 h3 h4 h5 h6
  all_goals try assumption
  obtain ⟨⟨b,d⟩,hd⟩ := hex
  cases b <;> fin_cases d <;> simp_all

/-- A candidate's direction is used exactly by incidences on its side. -/
def compatible (rs : List Port) (c : Port) : Bool :=
  rs.all (fun r => decide (r.2=c.2 ↔ r.1=c.1))

theorem compatible_iff (rs : List Port) (c : Port) :
    compatible rs c=true ↔ ∀r∈rs,r.2=c.2 ↔ r.1=c.1 := by
  simp [compatible]

def choose (rs : List Port) : Port := select (compatible rs)

theorem choose_valid (rs : List Port)
    (hex : ∃ c:Port, ∀r∈rs, r.2 =c.2 ↔ r.1 =c.1) :
    ∀r∈rs,r.2=(choose rs).2 ↔ r.1=(choose rs).1 := by
  apply (compatible_iff rs (choose rs)).mp
  apply select_valid
  obtain ⟨c,hc⟩ := hex
  exact ⟨c,(compatible_iff rs c).mpr hc⟩

/-- The canonical result depends only on the incidence set, not on its
enumeration order or repetitions. -/
theorem choose_congr (rs ts : List Port) (he : ∀ p, p∈rs ↔ p ∈ts) : choose rs=choose ts := by
  unfold choose
  congr 1
  funext c
  apply Bool.eq_iff_iff.mpr
  simp only [compatible_iff, he]

end GridHardness.DirectedPortSelection
