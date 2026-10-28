import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramGenerated

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

def entries (scopes : List (List ℕ)) : ℕ → ℕ → List Bool → List (ℕ × ℕ)
  | _,_,[] => []
  | v,z,high::rest => entries scopes (v+1) (if high then z else Step.next scopes v z) rest ++
      if high then [] else (Step.factors scopes v z).map fun e => (v,e)

theorem plans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    ∀ v z, Loop.plans scopes n v z mask = (entries scopes v z mask).map (fun p => [p.1,n+p.2]) := by
  induction mask with
  | nil => intros; rfl
  | cons high mask ih =>
      intro v z
      cases high <;> simp [Loop.plans,entries,Loop.rowPlans,ih,List.map_map]

theorem next_le (scopes : List (List ℕ)) (v z : ℕ) : z ≤ Step.next scopes v z := by
  unfold Step.next; split <;> omega

theorem counter_mono (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, z ≤ Loop.finalCounter scopes v z mask := by
  induction mask with
  | nil => intros; rfl
  | cons high mask ih =>
      intro v z
      cases high
      · exact (next_le scopes v z).trans (ih (v+1) (Step.next scopes v z))
      · exact ih (v+1) z

theorem next_le_add_one (scopes : List (List ℕ)) (v z : ℕ) :
    Step.next scopes v z ≤ z+1 := by
  unfold Step.next; split <;> omega

theorem counter_le (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, Loop.finalCounter scopes v z mask ≤ z+mask.length := by
  induction mask with
  | nil => intros; rfl
  | cons high mask ih =>
      intro v z
      have hnext := next_le_add_one scopes v z
      have ht := ih (v+1) (if high then z else Step.next scopes v z)
      cases high <;> simp only [Loop.finalCounter,ite_true,Bool.false_eq_true,ite_false,
        List.length_cons] at * <;> omega

theorem factor_lt_next (scopes : List (List ℕ)) (v z e : ℕ)
    (hz : scopes.length ≤ z) (he : e ∈ Step.factors scopes v z) :
    e < Step.next scopes v z := by
  by_cases h : Scan.indices scopes v = []
  · have heq : e = z := by simpa [Step.factors,h] using he
    subst e
    simp [Step.next,h]
  · have he' : e ∈ Scan.indices scopes v := by simpa [Step.factors,h] using he
    have hh := IncidencePlanSpec.incidentIndex_lt scopes v e he'
    simpa [Step.next,h] using hh.trans_le hz

theorem entry_bounds (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ n v z, v+mask.length ≤ n → scopes.length ≤ z →
      ∀ p ∈ entries scopes v z mask, p.1 < n ∧ p.2 < Loop.finalCounter scopes v z mask := by
  induction mask with
  | nil => simp [entries]
  | cons high mask ih =>
      intro n v z hn hz p hp
      have hnext := next_le scopes v z
      cases high
      · simp only [entries,Bool.false_eq_true,ite_false,List.mem_append] at hp
        rcases hp with hp|hp
        · exact ih n (v+1) (Step.next scopes v z) (by simp only [List.length_cons] at hn; omega)
            (hz.trans hnext) p hp
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
          exact ⟨by simp only [List.length_cons] at hn; omega,
            (factor_lt_next scopes v z e hz he).trans_le (counter_mono scopes mask (v+1) _)⟩
      · simp only [entries,ite_true,List.append_nil] at hp
        exact ih n (v+1) z (by simp only [List.length_cons] at hn; omega) hz p hp

theorem factors_length_le (scopes : List (List ℕ)) (v z : ℕ) :
    (Step.factors scopes v z).length ≤ scopes.length+1 := by
  by_cases h : Scan.indices scopes v = []
  · simp [Step.factors,h]
  · have hd := SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
    change (Scan.indices scopes v).length ≤ scopes.length at hd
    simpa [Step.factors,h] using hd.trans (Nat.le_succ _)

theorem entries_length_le (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, (entries scopes v z mask).length ≤ mask.length*(scopes.length+1) := by
  induction mask with
  | nil => intros; simp [entries]
  | cons high mask ih =>
      intro v z
      have ht := ih (v+1) (if high then z else Step.next scopes v z)
      have hf := factors_length_le scopes v z
      cases high <;> simp only [entries,ite_true,Bool.false_eq_true,ite_false,
        List.length_append,List.length_map,List.length_nil,List.length_cons] at * <;>
        nlinarith

theorem plans_length_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Loop.plans scopes n 0 scopes.length mask).length ≤ mask.length*(scopes.length+1) := by
  rw [plans_eq,List.length_map]
  exact entries_length_le scopes mask 0 scopes.length

def nativeEntries (scopes : List (List ℕ)) (mask : List Bool) := entries scopes 0 scopes.length mask
def factorCount (scopes : List (List ℕ)) (mask : List Bool) := Loop.finalCounter scopes 0 scopes.length mask
abbrev Incidences (scopes : List (List ℕ)) (mask : List Bool) := Fin (nativeEntries scopes mask).length
def owner (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) : Fin n :=
  ⟨((nativeEntries scopes mask).get i).1,
    (entry_bounds scopes mask n 0 scopes.length (by omega) le_rfl _ (List.get_mem _ i)).1⟩
def factor (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) : Fin (factorCount scopes mask) :=
  ⟨((nativeEntries scopes mask).get i).2,
    (entry_bounds scopes mask n 0 scopes.length (by omega) le_rfl _ (List.get_mem _ i)).2⟩
def seedIndices (n f : ℕ) := Packing.headsFirstIndices (List.finRange n) (List.finRange f)

theorem seedIndices_complete (n f : ℕ) : ∀ x, x ∈ seedIndices n f :=
  Packing.headsFirst_complete _ _ List.mem_finRange List.mem_finRange

theorem incidencePlan_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) :
    PackingIncidenceProgram.incidencePlan (owner scopes n mask hm) (factor scopes n mask hm)
      (seedIndices n (factorCount scopes mask)) i =
      [((nativeEntries scopes mask).get i).1,n+((nativeEntries scopes mask).get i).2] := by
  simp only [PackingIncidenceProgram.incidencePlan,seedIndices]
  rw [Packing.headsFirst_index_head _ _ _ (List.mem_finRange _),
    Packing.headsFirst_index_factor]
  simp only [List.length_finRange,SubexponentialSAT.LocalExpectation.indexCode,
    List.idxOf_finRange,owner,factor]

theorem incidencePlans_eq (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n) :
    PackingIncidenceProgram.incidencePlans (owner scopes n mask hm) (factor scopes n mask hm)
      (seedIndices n (factorCount scopes mask)) (List.finRange (nativeEntries scopes mask).length) =
      Loop.plans scopes n 0 scopes.length mask := by
  rw [plans_eq]
  simp only [PackingIncidenceProgram.incidencePlans]
  rw [show (List.finRange (nativeEntries scopes mask).length).map
      (PackingIncidenceProgram.incidencePlan (owner scopes n mask hm) (factor scopes n mask hm)
        (seedIndices n (factorCount scopes mask))) =
      List.ofFn (fun i : Incidences scopes mask =>
        [((nativeEntries scopes mask).get i).1,n+((nativeEntries scopes mask).get i).2]) by
      simp [List.ofFn_eq_map,incidencePlan_eq]]
  change List.ofFn ((fun p : ℕ × ℕ => [p.1,n+p.2]) ∘
    (nativeEntries scopes mask).get) = _
  rw [← List.map_ofFn,List.ofFn_get]
  rfl
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
