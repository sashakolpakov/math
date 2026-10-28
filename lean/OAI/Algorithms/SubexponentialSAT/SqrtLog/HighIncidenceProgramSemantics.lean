import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramBranches

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

abbrev suppliedScope (n : ℕ) (scopes : List (List ℕ)) :=
  (Subexp.IncidencePlanSpec.pattern n scopes).scope

theorem degree_suppliedScope (n : ℕ) (scopes : List (List ℕ)) (v : Fin n) :
    Incidence.degree (suppliedScope n scopes) v = degree scopes v.val := by
  have h := Subexp.IncidencePlanSpec.card_incident n scopes v
  rw [SlotAssignment.card_incident] at h
  exact h

theorem highPrefix_trueCount (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      ∑ v ∈ Finset.range n, if cut < degree scopes v then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : cut < degree scopes n
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using ih

theorem highPrefix_count_eq_card (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      (HighIncidence.high (suppliedScope n scopes) cut).card := by
  rw [highPrefix_trueCount, Finset.sum_range]
  simp only [HighIncidence.high, Finset.card_eq_sum_ones, Finset.sum_filter,
    degree_suppliedScope]

theorem computed_high_dimension (scopes : List (List ℕ)) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    Branches.trueCount
      (highPrefix scopes (HighIncidence.cutoff (suppliedScope n scopes) t) n) ≤ n / t := by
  rw [highPrefix_count_eq_card]
  simpa using HighIncidence.high_cutoff_card_le_div (suppliedScope n scopes) t
    (by simpa using hn) ht

/-- Empty scope families and unused variables produce low bits, not omitted
coordinates. In particular the physical output length remains n. -/
theorem empty_scopes_mask (cut n : ℕ) :
    highPrefix [] cut n = List.replicate n false := by
  induction n <;> simp [highPrefix, degree, Subexp.IncidencePlanSpec.degree,
    Subexp.IncidencePlanSpec.incidentIndices, Subexp.IncidencePlanSpec.incidenceFrom,
    List.replicate_succ, *]


/-- Even nonnormalized supplied records overcount rather than undercount mass.
This suffices for the high-dimension bound with the physically counted S. -/
theorem suppliedScope_card_le (n : ℕ) (scopes : List (List ℕ)) (e : Fin scopes.length) :
    (suppliedScope n scopes e).card ≤ (scopes.get e).length := by
  have hi : (suppliedScope n scopes e).image Fin.val ⊆ (scopes.get e).toFinset := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((Subexp.IncidencePlanSpec.mem_pattern_scope n scopes v e).mp hv)
  calc
    _ = ((suppliedScope n scopes e).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (scopes.get e).toFinset.card := Finset.card_le_card hi
    _ ≤ (scopes.get e).length := List.toFinset_card_le _

theorem suppliedScope_mass_le (n : ℕ) (scopes : List (List ℕ)) :
    HighIncidence.totalScope (suppliedScope n scopes) ≤ (scopes.map List.length).sum := by
  calc
    _ ≤ ∑ e : Fin scopes.length, (scopes.get e).length :=
      Finset.sum_le_sum (fun e _ => suppliedScope_card_le n scopes e)
    _ = (scopes.map List.length).sum := by
      rw [← Fin.sum_ofFn]
      change (List.ofFn (List.length ∘ scopes.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]

/-- The threshold may be computed from raw entry counts. Duplicates or
out-of-range supplied IDs cannot invalidate the dimension estimate. -/
theorem computed_high_dimension_rawMass (scopes : List (List ℕ)) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    Branches.trueCount
      (highPrefix scopes (((scopes.map List.length).sum * t) ⌈/⌉ n) n) ≤ n / t := by
  rw [highPrefix_count_eq_card]
  apply (Nat.le_div_iff_mul_le ht).mpr
  have hb : HighIncidence.totalScope (suppliedScope n scopes) * t ≤
      n * (((scopes.map List.length).sum * t) ⌈/⌉ n) := by
    calc
      _ ≤ (scopes.map List.length).sum * t := Nat.mul_le_mul_right _ (suppliedScope_mass_le n scopes)
      _ ≤ n * (((scopes.map List.length).sum * t) ⌈/⌉ n) :=
        (ceilDiv_le_iff_le_mul hn).mp le_rfl
  simpa only [Fintype.card_fin] using HighIncidence.high_card_mul_le
    (suppliedScope n scopes) (((scopes.map List.length).sum * t) ⌈/⌉ n) t (by simpa using hb)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
