import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DyadicReadiness

namespace OAI.Algorithms

/-!
# Dyadic readiness in Main's layout interface

The actual integer readiness test supplies all three numerical feasibility
conditions used by `SubexpMainLayoutSemantics`: the dimension threshold,
the universal-type threshold, and the normalized probability tail. The
parameter record is the canonical dyadic record, whose extension degree
and node count are definitionally `4` and `p^4 - 1`.

The separate bounded-incidence property of the input pattern remains a
property of the actual sparse leaf and its constructed scopes.
-/

namespace SubexponentialSAT.SubexpMainDyadicReadiness

open SubexpPackingParameters Subexp MulticolorTypes

/-- Convert the proved weighted tail to Main's exact probability-tail
condition, with its literal quartic node count and canonical degree. -/
theorem normalized_tail (k T : ℕ) (hk : 2 ≤ k) {n : ℕ}
    (hn : DyadicSchedule.Ready k T n) :
    let c := DyadicSchedule.parameters k T hk n (DyadicSchedule.ready_goodInput hn)
    SpectralRank.normalizedTail (r n) (p n^4 - 1 - 1)
      (TailInterval.intervalStart (r n) (p n^4 - 1) c.R) c.R ≤
        DyadicSchedule.tau n / (DyadicSchedule.delta k T n : ℚ) := by
  have hr := goodInput_r_ge_two (DyadicSchedule.ready_goodInput hn)
  change SpectralRank.normalizedTail (r n) (DyadicSchedule.Q n - 1)
    (DyadicSchedule.intervalStart k T n) (DyadicSchedule.R k T n) ≤ _
  exact (SpectralRank.normalizedTail_le_iff (r n) (DyadicSchedule.Q n - 1)
    (DyadicSchedule.intervalStart k T n) (DyadicSchedule.R k T n)
    (DyadicSchedule.delta k T n) (DyadicSchedule.tau n)
    (by omega) (DyadicSchedule.delta_pos k T n)).mpr
      (DyadicSchedule.weighted_tail hk hn)

/-- The checked dimension condition for the same canonical record. -/
theorem size (k T : ℕ) (hk : 2 ≤ k) {n : ℕ}
    (hn : DyadicSchedule.Ready k T n) :
    (DyadicSchedule.parameters k T hk n (DyadicSchedule.ready_goodInput hn)).Dstar ≤
      D n :=
  DyadicSchedule.ready_dimension hn

/-- The universal-type threshold in Main's literal `p^4 - 1` form. -/
theorem threshold (k T : ℕ) (hk : 2 ≤ k) {n : ℕ}
    (hn : DyadicSchedule.Ready k T n) :
    let c := DyadicSchedule.parameters k T hk n (DyadicSchedule.ready_goodInput hn)
    (Fintype.card (UniversalType (r n) (p n^4 - 1)
      (DyadicSchedule.delta k T n)) : ℚ)^3 *
        (1 + (DyadicSchedule.delta k T n * k : ℕ)) ≤
      DyadicSchedule.tau n^2 * c.Dstar :=
  DyadicSchedule.parameter_threshold k T hk (DyadicSchedule.ready_goodInput hn)

/-- One actual readiness witness discharges Main's quartic parameter and
all numerical layout premises. No layout or incidence bound is assumed. -/
theorem ready_conditions (k T : ℕ) (hk : 2 ≤ k) {n : ℕ}
    (hn : DyadicSchedule.Ready k T n) :
    let c := DyadicSchedule.parameters k T hk n (DyadicSchedule.ready_goodInput hn)
    c.h = 4 ∧ c.Dstar ≤ D n ∧
      (Fintype.card (UniversalType (r n) (p n^4 - 1)
        (DyadicSchedule.delta k T n)) : ℚ)^3 *
          (1 + (DyadicSchedule.delta k T n * k : ℕ)) ≤
        DyadicSchedule.tau n^2 * c.Dstar ∧
      SpectralRank.normalizedTail (r n) (p n^4 - 1 - 1)
        (TailInterval.intervalStart (r n) (p n^4 - 1) c.R) c.R ≤
          DyadicSchedule.tau n / (DyadicSchedule.delta k T n : ℚ) :=
  ⟨rfl, size k T hk hn, threshold k T hk hn, normalized_tail k T hk hn⟩

end SubexponentialSAT.SubexpMainDyadicReadiness

end OAI.Algorithms
