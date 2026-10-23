import StickKnots.Counting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Parameterized finite lower-bound wrapper

This is the arithmetic core of the stronger word-family lower bound.  The
choice `q ≈ log N`, the RSK lower bound for the generator set, Garside
uniqueness, and the two cited knot-theory theorems are deliberately left
outside; no asymptotic notation or claim of a matching order of growth is
encoded here.
-/

namespace StickKnots

open scoped BigOperators

/-- The generic squared finite Cauchy--Schwarz step used by the later
conditional RSK consequence. -/
theorem rsk_cauchy_count_bound {ι : Type*} (s : Finset ι) (a f : ι → ℝ) :
    (∑ i ∈ s, a i * f i) ^ 2 ≤
      (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, f i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s a f

/-- Natural-number form used directly for finite representation counts. -/
theorem rsk_cauchy_count_bound_nat {ι : Type*} (s : Finset ι) (a f : ι → ℕ) :
    (∑ i ∈ s, a i * f i) ^ 2 ≤
      (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, f i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s a f

/-- Once the three RSK/counting sum identities are supplied, Cauchy gives the exact
finite inequality `E² ≤ n! |G|`.  The RSK identities themselves remain
external hypotheses. -/
theorem rsk_generator_lower_from_identities
    {ι : Type*} (s : Finset ι) (a f : ι → ℕ) (E n generatorCount : ℕ)
    (hE : ∑ i ∈ s, a i * f i = E)
    (hGenerators : ∑ i ∈ s, a i ^ 2 = generatorCount)
    (hPermutation : ∑ i ∈ s, f i ^ 2 = n.factorial) :
    E ^ 2 ≤ n.factorial * generatorCount := by
  simpa [hE, hGenerators, hPermutation, Nat.mul_comm] using
    rsk_cauchy_count_bound_nat s a f

/-- The numerical Malyutin--Stupakov arc-index expression for the parameterized
word family, including the `max` in the cited statement. -/
def wordArcBudget (n q : ℕ) : ℕ := n * max 11 (q + 9) - 4

/-- The floor formula for the strand count; the later choice of `q` and its
asymptotic validity range are not encoded in this definition. -/
def lowerStrandCount (N q : ℕ) : ℕ := (2 * N + 15) / (3 * (q + 9))

theorem lowerStrandCount_capacity (N q : ℕ) :
    3 * (lowerStrandCount N q * (q + 9)) ≤ 2 * N + 15 := by
  calc
    3 * (lowerStrandCount N q * (q + 9)) =
        (3 * (q + 9)) * ((2 * N + 15) / (3 * (q + 9))) := by
      unfold lowerStrandCount
      ring
    _ ≤ 2 * N + 15 := Nat.mul_div_le _ _

theorem wordArcBudget_eq_largeQ {n q : ℕ} (hq : 2 ≤ q) :
    wordArcBudget n q = n * (q + 9) - 4 := by
  unfold wordArcBudget
  rw [max_eq_right]
  omega

theorem wordArcBudget_pred_eq {n q : ℕ} (hq : 2 ≤ q)
    (hlarge : 5 ≤ n * (q + 9)) :
    wordArcBudget n q - 1 = n * (q + 9) - 5 := by
  rw [wordArcBudget_eq_largeQ hq]
  omega

/-- On the `q ≥ 2` branch used asymptotically, the exact `15`-unit slack
calculation fits the predecessor of the cited arc-index expression into the
numerical Huh--Oh budget.  The Huh--Oh theorem itself is not represented. -/
theorem wordArcBudget_fits
    {N n q : ℕ} (hq : 2 ≤ q)
    (hcapacity : 3 * (n * (q + 9)) ≤ 2 * N + 15) :
    3 * (wordArcBudget n q - 1) ≤ 2 * N := by
  unfold wordArcBudget
  rw [max_eq_right]
  · omega
  · omega

/-- Pure finite counting transfer.  `garsideEndpointFiber` packages Garside
uniqueness and pigeonhole and already contains the `n!` denominator.  RSK is
used separately to lower-bound `generatorCount`.  The next two hypotheses are
the Malyutin--Stupakov and Huh--Oh count transfers; `forgetOrientation` is a
fourth supplied inequality already containing the factor `2`. -/
theorem wordFamily_count_transfer
    {n q generatorCount pureWordCount distinctOrientedKnots
      orientedNStickKnots stickKnotCount : ℕ}
    (garsideEndpointFiber :
      generatorCount ^ q ≤ n.factorial * pureWordCount)
    (malyutinStupakovInjection : pureWordCount ≤ distinctOrientedKnots)
    (huhOhStickBudgetTransfer :
      distinctOrientedKnots ≤ orientedNStickKnots)
    (forgetOrientation : orientedNStickKnots ≤ 2 * stickKnotCount) :
    generatorCount ^ q ≤ 2 * n.factorial * stickKnotCount := by
  calc
    generatorCount ^ q ≤ n.factorial * pureWordCount := garsideEndpointFiber
    _ ≤ n.factorial * distinctOrientedKnots :=
      Nat.mul_le_mul_left n.factorial malyutinStupakovInjection
    _ ≤ n.factorial * orientedNStickKnots :=
      Nat.mul_le_mul_left n.factorial huhOhStickBudgetTransfer
    _ ≤ n.factorial * (2 * stickKnotCount) :=
      Nat.mul_le_mul_left n.factorial forgetOrientation
    _ = 2 * n.factorial * stickKnotCount := by ring

/-- Conditional arithmetic lower wrapper.  It propagates four supplied count
inequalities and certifies the numerical budget and real-valued rearrangement
`generatorCount^q / (2 n!) ≤ stickKnotCount`. -/
theorem wordFamily_lower_from_external_inputs
    {N n q generatorCount pureWordCount distinctOrientedKnots
      orientedNStickKnots stickKnotCount : ℕ}
    (hq : 2 ≤ q)
    (hcapacity : 3 * (n * (q + 9)) ≤ 2 * N + 15)
    (garsideEndpointFiber :
      generatorCount ^ q ≤ n.factorial * pureWordCount)
    (malyutinStupakovInjection : pureWordCount ≤ distinctOrientedKnots)
    (huhOhStickBudgetTransfer :
      distinctOrientedKnots ≤ orientedNStickKnots)
    (forgetOrientation : orientedNStickKnots ≤ 2 * stickKnotCount) :
    3 * (wordArcBudget n q - 1) ≤ 2 * N ∧
      (generatorCount : ℝ) ^ q / (2 * (n.factorial : ℝ)) ≤ stickKnotCount := by
  constructor
  · exact wordArcBudget_fits hq hcapacity
  · have hnat := wordFamily_count_transfer garsideEndpointFiber malyutinStupakovInjection
      huhOhStickBudgetTransfer forgetOrientation
    have hreal : (generatorCount : ℝ) ^ q ≤
        (2 : ℝ) * (n.factorial : ℝ) * (stickKnotCount : ℝ) := by
      exact_mod_cast hnat
    rw [div_le_iff₀ (by positivity)]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hreal

/-- The same conditional lower wrapper with the strand count fixed to the
floor formula.  The caller supplies `q ≥ 2` and the four external count
inequalities, but no separate capacity hypothesis. -/
theorem wordFamily_lower_at_floor_from_external_inputs
    {N q generatorCount pureWordCount distinctOrientedKnots
      orientedNStickKnots stickKnotCount : ℕ}
    (hq : 2 ≤ q)
    (garsideEndpointFiber :
      generatorCount ^ q ≤ (lowerStrandCount N q).factorial * pureWordCount)
    (malyutinStupakovInjection : pureWordCount ≤ distinctOrientedKnots)
    (huhOhStickBudgetTransfer :
      distinctOrientedKnots ≤ orientedNStickKnots)
    (forgetOrientation : orientedNStickKnots ≤ 2 * stickKnotCount) :
    3 * (wordArcBudget (lowerStrandCount N q) q - 1) ≤ 2 * N ∧
      (generatorCount : ℝ) ^ q /
        (2 * ((lowerStrandCount N q).factorial : ℝ)) ≤ stickKnotCount := by
  exact wordFamily_lower_from_external_inputs
    hq (lowerStrandCount_capacity N q) garsideEndpointFiber
    malyutinStupakovInjection huhOhStickBudgetTransfer forgetOrientation

end StickKnots
