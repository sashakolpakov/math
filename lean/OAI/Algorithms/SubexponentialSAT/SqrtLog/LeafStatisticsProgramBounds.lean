import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramBoot

namespace OAI.Algorithms

/-! Polynomial physical cost and basic exact output identities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def uniformStepBudget (scopes : List (List ℕ)) (n : ℕ) :=
  1000*((scopeBits scopes).length+scopes.length+n+1)^2+50*(scopes.length+1)+50

theorem stepBudget_le (scopes : List (List ℕ)) (n v : ℕ) (hv : v ≤ n) :
    stepBudget scopes v ≤ uniformStepBudget scopes n := by
  have hc := SubexpIncidenceSlotProgram.budget_le scopes scopes.length v
    ((scopeBits scopes).length+scopes.length+n)
    (by change (scopeBits scopes).length ≤ (scopeBits scopes).length+scopes.length+n; omega)
    (by omega) (by omega)
  have hd : degree scopes v ≤ scopes.length :=
    SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
  dsimp [stepBudget,uniformStepBudget]
  omega

theorem variableBudget_le (scopes : List (List ℕ)) (n v : ℕ) (mask : List Bool)
    (hn : v+mask.length ≤ n) :
    variableBudget scopes v mask ≤ mask.length*(uniformStepBudget scopes n+1)+1 := by
  induction mask generalizing v with
  | nil => simp [variableBudget]
  | cons b bs ih =>
    have hs := stepBudget_le scopes n v (by simp at hn; omega)
    have ht := ih (v+1) (by simp at hn; omega)
    simp only [variableBudget,List.length_cons]
    nlinarith

theorem bootBudget_le (scopes : List (List ℕ)) (mask : List Bool) :
    bootBudget scopes mask ≤ 10*(scopeBits scopes).length+7*mask.length+12 := by
  have h := SubexpSunflowerProgram.CountRecords.steps_le_encoded
    (scopes.map SubexpIncidenceSlotProgram.scopeBytes)
  rw [SubexpIncidenceSlotProgram.encode_map] at h
  change SubexpSunflowerProgram.CountRecords.steps (scopes.map SubexpIncidenceSlotProgram.scopeBytes) ≤
    3*(scopeBits scopes).length+4 at h
  dsimp [SubexpSunflowerProgram.CountRecords.steps] at h
  dsimp [bootBudget]
  omega

theorem program_primitive (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (10*(scopeBits scopes).length+7*mask.length+mask.length*(uniformStepBudget scopes mask.length+1)+15))
      (primitiveCfg program ((initial r scopes mask).withPC (some program.entry)))
      (primitiveCfg program ((variableState rf scopes mask.length [] mask
        (variableTotals scopes 0 mask zeroTotals)).withPC none)) := by
  obtain ⟨rf,hr⟩ := program_runsIn r scopes mask
  have hb := bootBudget_le scopes mask
  have hv := variableBudget_le scopes mask.length 0 mask (by omega)
  refine ⟨rf,BitProgram.primitive_execution program (hr.mono ?_)⟩
  omega

theorem variableTotals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free+mask.count false := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals,Totals.add,ih,Nat.add_comm,Nat.add_left_comm]

theorem variableTotals_covers (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals)
    (ht : t.free ≤ t.incidences) :
    (variableTotals scopes v mask t).free ≤ (variableTotals scopes v mask t).incidences := by
  induction mask generalizing v t with
  | nil => exact ht
  | cons b bs ih =>
    cases b with
    | true => exact ih (v+1) t ht
    | false =>
      apply ih (v+1) (t.add (degree scopes v))
      have h := le_max_left 1 (degree scopes v)
      dsimp [Totals.add]
      omega

theorem actual_freeCount (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zeroTotals).free = mask.count false := by
  simpa [zeroTotals] using variableTotals_free scopes 0 mask zeroTotals

theorem actual_incidences_cover (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zeroTotals).free ≤
      (variableTotals scopes 0 mask zeroTotals).incidences :=
  variableTotals_covers scopes 0 mask zeroTotals (by rfl)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
