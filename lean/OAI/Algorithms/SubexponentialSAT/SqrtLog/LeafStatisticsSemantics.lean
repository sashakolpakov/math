import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsTotals
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsNeutral

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

/-- The native mask uses `true` for a removed (high-incidence) coordinate. -/
def highMask (mask : List Bool) : Finset (Fin mask.length) :=
  Finset.univ.filter fun i => mask.get i = true

abbrev Free (mask : List Bool) := {v : Fin mask.length // v ∉ highMask mask}

def residualScope (scopes : List (List ℕ)) (mask : List Bool) :
    Fin scopes.length → Finset (Free mask) :=
  remainingScope (highMask mask) (Subexp.IncidencePlanSpec.pattern mask.length scopes).scope

def completedScope (scopes : List (List ℕ)) (mask : List Bool) :=
  neutralScope (residualScope scopes mask)

@[simp] theorem mem_highMask (mask : List Bool) (i : Fin mask.length) :
    i ∈ highMask mask ↔ mask.get i = true := by simp [highMask]

@[simp] theorem free_bit (mask : List Bool) (i : Free mask) :
    mask.get i.val = false := by
  have h := i.property
  simp only [mem_highMask] at h
  cases hb : mask.get i.val <;> simp_all

theorem scanSum_eq_free_sum (f : ℕ → ℕ) (mask : List Bool) :
    scanSum f 0 mask = ∑ i : Free mask, f i.val.val := by
  unfold scanSum
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin mask.length => i ∉ highMask mask), f i.val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_highMask, List.get_eq_getElem]
      by_cases hb : mask[i.val] = true <;> simp [hb]
    _ = _ := Finset.sum_subtype _ (by intro i; simp) _

theorem pattern_degree (scopes : List (List ℕ)) (n : ℕ) (v : Fin n) :
    Incidence.degree (Subexp.IncidencePlanSpec.pattern n scopes).scope v = degree scopes v.val := by
  calc
    _ = Fintype.card (SlotAssignment.Incident (Subexp.IncidencePlanSpec.pattern n scopes) v) := by
      simp only [SlotAssignment.card_incident, Incidence.degree, Incidence.incident]
    _ = _ := Subexp.IncidencePlanSpec.card_incident n scopes v

@[simp] theorem residual_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (residualScope scopes mask) v = degree scopes v.val.val := by
  rw [residualScope, degree_remainingScope]
  exact pattern_degree scopes mask.length v.val

@[simp] theorem completed_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (completedScope scopes mask) v = max 1 (degree scopes v.val.val) := by
  rw [completedScope, neutral_degree_eq, residual_degree]

/-- This literal zero record is definitionally the native boot record. -/
def zero : Totals := ⟨0, 0, 0, 0⟩

theorem free_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).free = Fintype.card (Free mask) := by
  rw [totals_free, scanSum_eq_free_sum]
  simp [zero]

theorem incidences_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).incidences = totalScope (completedScope scopes mask) := by
  rw [totals_incidences, scanSum_eq_free_sum]
  simp only [zero, Nat.zero_add]
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [completed_degree]

theorem uncovered_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).uncovered = (uncovered (residualScope scopes mask)).card := by
  rw [totals_uncovered, scanSum_eq_free_sum]
  simp [zero, uncovered]

theorem occurrence_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).occurrence =
      Finset.univ.sup (Incidence.degree (completedScope scopes mask)) := by
  apply Nat.le_antisymm
  · rw [totals_occurrence_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i hi
    simp only [List.get_eq_getElem] at hi
    let v : Free mask := ⟨i, by simp [hi]⟩
    simpa only [Nat.zero_add, completed_degree] using
      (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v))
  · apply Finset.sup_le
    intro v _
    have h := (totals_occurrence_le_iff scopes 0 mask zero
      (variableTotals scopes 0 mask zero).occurrence).mp le_rfl
    simpa only [Nat.zero_add, completed_degree] using h.2 v.val (free_bit mask v)

theorem factors_exact (scopes : List (List ℕ)) (mask : List Bool) :
    scopes.length + (variableTotals scopes 0 mask zero).uncovered =
      Fintype.card (Fin scopes.length ⊕ uncovered (residualScope scopes mask)) := by
  rw [uncovered_exact]
  simp

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
