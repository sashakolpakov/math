import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyProducedGuards
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramSemantics

namespace OAI.Algorithms

/-! Guard success for the actual forward mask computed from all supplied raw
scopes.  The high cutoff counts raw entries, including harmless overcounts. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafStatisticsSemantics HighIncidenceProgram

private theorem scanSum_ones_eq_count (mask : List Bool) (v : ℕ) :
    scanSum (fun _ => 1) v mask = mask.count false := by
  induction mask generalizing v with
  | nil => simp
  | cons b bs ih => cases b <;> simp [scanSum_cons, ih, Nat.add_comm]

theorem measured_free_eq_false_count (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free = mask.count false := by
  simp only [measured, totals_free, LeafStatisticsSemantics.zero, Nat.zero_add]
  exact scanSum_ones_eq_count mask 0

private theorem count_bool_partition (mask : List Bool) :
    mask.count false + mask.count true = mask.length := by
  induction mask with
  | nil => simp
  | cons b bs ih => cases b <;> simp [] <;> omega

theorem measured_highPrefix_free (scopes : List (List ℕ)) (cut n : ℕ) :
    (measured scopes (highPrefix scopes cut n).reverse).free =
      n - Branches.trueCount (highPrefix scopes cut n) := by
  rw [measured_free_eq_false_count, List.count_reverse]
  have hc := count_bool_partition (highPrefix scopes cut n)
  have hl := highPrefix_length scopes cut n
  have ht := Subexp.PaddedCompletion.trueCount_eq_count (highPrefix scopes cut n)
  change Branches.trueCount (highPrefix scopes cut n) =
    (highPrefix scopes cut n).count true at ht
  omega

def forwardHighMask (scopes : List (List ℕ)) (n τ : ℕ) : List Bool :=
  (highPrefix scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n).reverse

theorem forwardHighMask_length (scopes : List (List ℕ)) (n τ : ℕ) :
    (forwardHighMask scopes n τ).length = n := by
  simp [forwardHighMask]

theorem forwardHighMask_retains_half (scopes : List (List ℕ)) (n τ : ℕ)
    (hn : 0 < n) (hτ : 2 ≤ τ) :
    n ≤ 2*(measured scopes (forwardHighMask scopes n τ)).free := by
  have hpos : 0 < τ := by omega
  have h := computed_high_dimension_rawMass scopes n τ hn hpos
  have hm := (Nat.le_div_iff_mul_le hpos).mp h
  have ht := Nat.mul_le_mul_left
    (Branches.trueCount (highPrefix scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n)) hτ
  have he := measured_highPrefix_free scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n
  change (measured scopes (forwardHighMask scopes n τ)).free = _ at he
  omega

theorem highThreshold_ge_two (n : ℕ) : 2 ≤ Nat.sqrt (Asymptotic.L n)+1 := by
  have h := Nat.sqrt_pos.mpr (Asymptotic.L_pos n)
  omega

theorem highBranchCount_le_sqrt (scopes : List (List ℕ)) (n : ℕ) (hn : 0 < n) :
    (Branches.trueCount (highPrefix scopes
      (((scopes.map List.length).sum*(Nat.sqrt (Asymptotic.L n)+1)) ⌈/⌉ n) n) : ℝ) ≤
      (n : ℝ) / Real.sqrt (Asymptotic.L n : ℝ) := by
  let τ := Nat.sqrt (Asymptotic.L n)+1
  let H := Branches.trueCount (highPrefix scopes
    (((scopes.map List.length).sum*τ) ⌈/⌉ n) n)
  have hτ : 0 < τ := by dsimp [τ]; omega
  have hcount : H*τ ≤ n :=
    (Nat.le_div_iff_mul_le hτ).mp (computed_high_dimension_rawMass scopes n τ hn hτ)
  have hroot : Real.sqrt (Asymptotic.L n : ℝ) ≤ (τ : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hs : Asymptotic.L n ≤ τ^2 := (Nat.lt_succ_sqrt' (Asymptotic.L n)).le
    exact_mod_cast hs
  have hpos : 0 < Real.sqrt (Asymptotic.L n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Asymptotic.L_pos n)
  have hc : (H : ℝ)*(τ : ℝ) ≤ n := by exact_mod_cast hcount
  change (H : ℝ) ≤ (n : ℝ) / Real.sqrt (Asymptotic.L n : ℝ)
  apply (le_div_iff₀ hpos).mpr
  exact (mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ H)).trans hc

/-- The large-input cutoff is uniform in every raw scope family and mark.
Only their explicit polylogarithmic upper resource bounds are supplied by
the caller; half-retention and all nondegeneracy guards are derived here. -/
theorem eventually_forwardHighMask_guards (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (clauses width : ℕ),
      let mask := forwardHighMask scopes n (Nat.sqrt (Asymptotic.L n)+1)
      0 < clauses → (∀ row ∈ scopes, row.Nodup) →
      (measured scopes mask).occurrence ≤ C*Asymptotic.L n^q →
      measuredArity scopes mask ≤ C*Asymptotic.L n^q →
      LeafParametersProgram.Guard (measuredParameterInput scopes mask clauses width) := by
  filter_upwards [eventually_measured_guards C q, eventually_ge_atTop (1 : ℕ)]
    with n hn hnpos scopes clauses width
  dsimp only
  intro hcl hnodup hB ha
  exact hn scopes _ clauses width (forwardHighMask_length _ _ _)
    (forwardHighMask_retains_half _ _ _ (by omega) (highThreshold_ge_two n))
    hcl hnodup hB ha

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
