/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRun
public import GridHardness.SatCrossingHorizontalInterface

/-!
# Corrected SAT Interval Horizontal

The retained horizontal interface applies to actual consecutive requests
of the interval sweep. A request on a different old line selects a transported
bundle, disjoint from the entire newest tile, not merely its active XOR.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.Horizontal
open XorLineRegistry XorLineSchedule XorLine

variable {n : Nat} (s : IntervalState n) (a : Fin n) (line height : Nat)
variable (hc : s.Covered line height)

def latest (v : XorLine.Vertex 4) : (s.cross a line height hc).Vertex := .inr v

theorem latest_injective : Function.Injective (latest s a line height hc) :=
  Sum.inr_injective

theorem latest_adj (u v : XorLine.Vertex 4) :
    (s.cross a line height hc).adj (latest s a line height hc u)
      (latest s a line height hc v) ↔ Adj 4 u v := Iff.rfl

theorem latest_active (k : Fin 8) :
    (s.cross a line height hc).positioned.registry.xors.embed a k =
      latest s a line height hc (x 0 k) :=
  s.positioned.registry.crossXor_self a (s.select line height hc).val k

variable (nextLine nextHeight : Nat)
variable (hn : (s.cross a line height hc).Covered nextLine nextHeight)

/-- The two freshly split intervals both belong to the previous line.
A different requested line must therefore select a transported old bundle. -/
theorem select_transported (hne : nextLine ≠ line) :
    ∃ b : {c : s.BundleId // c ≠ (s.select line height hc).val},
      ((s.cross a line height hc).select nextLine nextHeight hn).val = .inl b := by
  have hs := ((s.cross a line height hc).select nextLine nextHeight hn).property.1
  cases he : ((s.cross a line height hc).select nextLine nextHeight hn).val with
  | inl b => exact ⟨b,rfl⟩
  | inr side =>
    rw [he] at hs
    have hp := (s.select line height hc).property.1
    cases side <;> change (s.positioned.segments (s.select line height hc).val).line = nextLine at hs
    all_goals exact False.elim (hne (hs.symm.trans hp))

def nextBundle : Bundle (s.cross a line height hc).adj 4 :=
  (s.cross a line height hc).positioned.registry.bundles
    ((s.cross a line height hc).select nextLine nextHeight hn).val

/-- All forty-eight fresh vertices avoid both endpoint sets of the next
selected bundle. This discharges the stronger hypotheses of the geometric
retained-tile interface. -/
theorem latest_ne_endpoint (hne : nextLine ≠ line) (i : Fin 4) (v : XorLine.Vertex 4) :
    latest s a line height hc v ≠ (nextBundle s a line height hc nextLine nextHeight hn).source i ∧
    latest s a line height hc v ≠ (nextBundle s a line height hc nextLine nextHeight hn).target i := by
  obtain ⟨b,hb⟩ := select_transported s a line height hc nextLine nextHeight hn hne
  unfold nextBundle
  rw [hb]
  change latest s a line height hc v ≠
      (s.positioned.registry.crossBundle a (s.select line height hc).val b.val).source i ∧
    latest s a line height hc v ≠
      (s.positioned.registry.crossBundle a (s.select line height hc).val b.val).target i
  have hs := s.positioned.registry.crossBundle_other a (s.select line height hc).val
    b.val b.property (i,false)
  have ht := s.positioned.registry.crossBundle_other a (s.select line height hc).val
    b.val b.property (i,true)
  change (s.positioned.registry.crossBundle a (s.select line height hc).val b.val).source i = _ at hs
  change (s.positioned.registry.crossBundle a (s.select line height hc).val b.val).target i = _ at ht
  rw [hs,ht]
  constructor
  · intro h
    cases h
  · intro h
    cases h

/-- The forty vertices of the preceding tile survive with these exact
identities in the actual next state. -/
def kept (u : SatCrossingHorizontal.RetainedVertex) :
    ((s.cross a line height hc).cross a nextLine nextHeight hn).Vertex :=
  .inl ⟨.inl (latest s a line height hc u.val),
    Bundle.old_not_in_sourceMarker _ _ (by
      intro k he
      rw [latest_active] at he
      exact SatCrossingHorizontal.retained_ne_zero u k
        ((latest_injective s a line height hc) he))⟩

theorem kept_injective : Function.Injective (kept s a line height hc nextLine nextHeight hn) := by
  intro u v h
  apply Subtype.ext
  exact (latest_injective s a line height hc)
    (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj h)))

theorem incoming_interface (hne : nextLine ≠ line)
    (u : SatCrossingHorizontal.RetainedVertex) (v : XorLine.Vertex 4) :
    ((s.cross a line height hc).cross a nextLine nextHeight hn).adj
      (kept s a line height hc nextLine nextHeight hn u) (.inr v) ↔
      u.val = row 0 false ∧ v = inputPort 4 (.inl false) := by
  have h := SatCrossingHorizontal.incoming_interface
    (nextBundle s a line height hc nextLine nextHeight hn)
    (latest s a line height hc) (latest_injective s a line height hc)
    (latest_adj s a line height hc)
    (fun i w => (latest_ne_endpoint s a line height hc nextLine nextHeight hn hne i w).1)
    (fun i w => (latest_ne_endpoint s a line height hc nextLine nextHeight hn hne i w).2) u v
  change (∃ p, Subdivision.Adj _ _ _ (.inl (latest s a line height hc u.val))
    (sourceMarker (fun k => latest s a line height hc (x 0 k)) (Source.inputPort 4 p)) ∧
      v = inputPort 4 p) ↔ _ at h
  change (∃ p, Subdivision.Adj _ _ _ (.inl (latest s a line height hc u.val))
    (sourceMarker ((s.cross a line height hc).positioned.registry.xors.embed a)
      (Source.inputPort 4 p)) ∧ v = inputPort 4 p) ↔ _
  have he : (s.cross a line height hc).positioned.registry.xors.embed a =
      (fun k => latest s a line height hc (x 0 k)) :=
    funext (latest_active s a line height hc)
  rw [he]
  exact h

theorem outgoing_interface (hne : nextLine ≠ line)
    (u : SatCrossingHorizontal.RetainedVertex) (v : XorLine.Vertex 4) :
    ((s.cross a line height hc).cross a nextLine nextHeight hn).adj (.inr v)
      (kept s a line height hc nextLine nextHeight hn u) ↔
      v = outputPort 4 (.inl false) ∧ u.val = row 0 true := by
  have h := SatCrossingHorizontal.outgoing_interface
    (nextBundle s a line height hc nextLine nextHeight hn)
    (latest s a line height hc) (latest_injective s a line height hc)
    (latest_adj s a line height hc)
    (fun i w => (latest_ne_endpoint s a line height hc nextLine nextHeight hn hne i w).1)
    (fun i w => (latest_ne_endpoint s a line height hc nextLine nextHeight hn hne i w).2) u v
  change (∃ p, Subdivision.Adj _ _ _
    (sourceMarker (fun k => latest s a line height hc (x 0 k)) (Source.outputPort 4 p))
    (.inl (latest s a line height hc u.val)) ∧ v = outputPort 4 p) ↔ _ at h
  change (∃ p, Subdivision.Adj _ _ _
    (sourceMarker ((s.cross a line height hc).positioned.registry.xors.embed a)
      (Source.outputPort 4 p)) (.inl (latest s a line height hc u.val)) ∧
      v = outputPort 4 p) ↔ _
  have he : (s.cross a line height hc).positioned.registry.xors.embed a =
      (fun k => latest s a line height hc (x 0 k)) :=
    funext (latest_active s a line height hc)
  rw [he]
  exact h

end GridHardness.CorrectedSatInterval.Horizontal
