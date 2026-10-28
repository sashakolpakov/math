import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasis
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

namespace OAI.Algorithms

/-!
# The complete Main local-basis cost at the scheduled parameters

The native search bound is combined with the actual wrapper instructions:
copying and converting the stored binary R word, and clearing the two
derived unary words and the preceding output. The selected input word is
bounded separately; no bound on the pending leaf stream is used.
-/

namespace SubexponentialSAT.SubexpMainLocalBasis

open Filter SubexpMainProgram SubexpLayoutPorts SubexpPackingParameters

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

theorem executionBound_eq {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (hcounter : CounterPrograms.value (a.stacks (persistent es 25)) = coefficients.length) :
    executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet =
      Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet +
      32 * (coefficients.length + 1) * ((a.stacks (persistent es 25)).length + 1) +
      7 * (a.stacks (persistent es 25)).length + 2 * coefficients.length +
      2 * (a.stacks (ordinary alloc 111)).length +
      2 * (a.stacks (master alloc 14)).length + 2 * (Q * r) + 50 := by
  unfold executionBound bound
  rw [SubexpLocalBasisControl.bound_eq, hcounter]
  have hc : (context alloc hregs a).length = a.stacks (ordinary alloc 111) := rfl
  simp only [hc, Subexp.TypeIndexProgram.unary, List.length_replicate]

/-- A fixed-degree bound for all wrapper work when both old output words
are empty. The bit length `b` is the actual stored R word, even if padded. -/
theorem wrapper_work_le {R r Q b L C d : ℕ}
    (hR : R ≤ L) (hr : r ≤ L) (hQ : Q ≤ L)
    (hb : b ≤ C * (L + 1)^d) :
    32 * (R + 1) * (b + 1) + 7 * b + 2 * R + 2 * (Q * r) + 50 ≤
      100 * (C + 1) * (L + 1)^(d + 2) := by
  have hp : 1 ≤ (L + 1)^d := Nat.one_le_pow _ _ (by omega)
  have hx : 1 ≤ (L + 1)^(d + 2) := Nat.one_le_pow _ _ (by omega)
  have hb' : b + 1 ≤ (C + 1) * (L + 1)^d := by nlinarith
  have hp' : (L + 1)^d ≤ (L + 1)^(d + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hl : L ≤ (L + 1)^(d + 2) := by
    have := Nat.pow_le_pow_right (by omega : 0 < L + 1) (by omega : 1 ≤ d + 2)
    simp only [pow_one] at this
    exact (Nat.le_succ L).trans this
  have hmain : (R + 1) * (b + 1) ≤ (C + 1) * (L + 1)^(d + 2) := by
    calc
      (R + 1) * (b + 1) ≤ (L + 1) * ((C + 1) * (L + 1)^d) :=
        Nat.mul_le_mul (by omega) hb'
      _ = (C + 1) * (L + 1)^(d + 1) := by rw [pow_succ]; ring
      _ ≤ (C + 1) * (L + 1)^(d + 2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hb'' : b ≤ (C + 1) * (L + 1)^(d + 2) :=
    hb.trans ((Nat.mul_le_mul_left C hp').trans (Nat.mul_le_mul_right _ (by omega)))
  have hR' : R ≤ (C + 1) * (L + 1)^(d + 2) :=
    (hR.trans hl).trans (by nlinarith)
  have hQr : Q * r ≤ (C + 1) * (L + 1)^(d + 2) := by
    calc
      Q * r ≤ (L + 1) * (L + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (L + 1)^2 := (pow_two _).symm
      _ ≤ (L + 1)^(d + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (C + 1) * (L + 1)^(d + 2) := by nlinarith
  have hone : 1 ≤ (C + 1) * (L + 1)^(d + 2) := by nlinarith
  nlinarith only [hmain, hb'', hR', hQr, hone]

/-- The constant is fixed before the formula and its variable count. -/
def wrapperConstant (factor C : ℕ) : ℕ := factor * 100 * (C + 1) + 1

theorem executionBound_le_runtime {er es : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (factor C d L n : ℕ)
    (hcounter : CounterPrograms.value (a.stacks (persistent es 25)) = coefficients.length)
    (hR : coefficients.length ≤ L) (hrL : r ≤ L) (hQL : Q ≤ L)
    (hbits : (a.stacks (persistent es 25)).length ≤ C * (L + 1)^d)
    (h111 : a.stacks (ordinary alloc 111) = [])
    (hout : a.stacks (master alloc 14) = [])
    (hnative : ((factor * Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ)
      p hr hQ coefficients alphabet : ℕ) : ℝ) ≤ (2 : ℝ)^SubexpComputation.scale n) :
    ((factor * executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet : ℕ) : ℝ) ≤
      SubexpComputation.runtimeBound (wrapperConstant factor C : ℝ) 1 (d + 2) L n := by
  have hw := wrapper_work_le hR hrL hQL hbits
  have he : executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet ≤
      Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet +
        100 * (C + 1) * (L + 1)^(d + 2) := by
    rw [executionBound_eq alloc hregs a p hr hQ coefficients alphabet hcounter,
      h111, hout]
    simp only [List.length_nil, mul_zero, add_zero]
    omega
  have hm := Nat.mul_le_mul_left factor he
  have hcast :
      ((factor * executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet : ℕ) : ℝ) ≤
      ((factor * Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ)
        p hr hQ coefficients alphabet : ℕ) : ℝ) +
      (factor : ℝ) * 100 * ((C : ℝ) + 1) * ((L : ℝ) + 1)^(d + 2) := by
    have hcast0 := (Nat.cast_le (α := ℝ)).mpr hm
    push_cast at hcast0
    push_cast
    convert hcast0 using 1
    all_goals ring
  have hpow : 1 ≤ ((L : ℝ) + 1)^(d + 2) :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
  have hexp : 1 ≤ (2 : ℝ)^SubexpComputation.scale n :=
    Real.one_le_rpow (by norm_num) (SubexpComputation.scale_nonneg n)
  calc
    _ ≤ (2 : ℝ)^SubexpComputation.scale n +
        (factor : ℝ) * 100 * ((C : ℝ) + 1) * ((L : ℝ) + 1)^(d + 2) :=
      hcast.trans (add_le_add_left hnative _)
    _ ≤ ((L : ℝ) + 1)^(d + 2) * (2 : ℝ)^SubexpComputation.scale n +
        ((factor : ℝ) * 100 * ((C : ℝ) + 1) * ((L : ℝ) + 1)^(d + 2)) *
          (2 : ℝ)^SubexpComputation.scale n := by
      apply add_le_add
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow (le_trans (by norm_num) hexp)
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (by positivity :
          0 ≤ (factor : ℝ) * 100 * ((C : ℝ) + 1) * ((L : ℝ) + 1)^(d + 2))
    _ = SubexpComputation.runtimeBound (wrapperConstant factor C : ℝ) 1 (d + 2) L n := by
      simp only [SubexpComputation.runtimeBound, wrapperConstant, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, one_mul]
      ring

/-- Uniformly over all actual Main entries with the selected setup-word
bound. The following state adapter derives the two empty words and carries
the R bytes from the real preceding stages. -/
theorem eventually_executionBound_le (k T factor C d : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (er es : ℕ) (alloc : Allocation es) (hregs : 16 ≤ er)
      (a : MainState er es) (L : ℕ) (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
      (coefficients alphabet : List (ZMod (p n))),
      coefficients.length = DyadicSchedule.R k T n → alphabet.length = p n →
      CounterPrograms.value (a.stacks (persistent es 25)) = coefficients.length →
      (a.stacks (persistent es 25)).length ≤ C * (L + 1)^d →
      a.stacks (ordinary alloc 111) = [] → a.stacks (master alloc 14) = [] → n ≤ L →
      ((factor * executionBound (Δ := DyadicSchedule.delta k T n)
        alloc hregs a (p n) hr hQ coefficients alphabet : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound (wrapperConstant factor C : ℝ) 1 (d + 2) L n := by
  filter_upwards [Subexp.LocalBasisBatchScheduleBounds.eventually_sourceBudget_le_scale k T factor,
    Subexp.LocalBasisBatchScheduleBounds.block_powers k T 1,
    eventually_goodInput] with n hnative hN hn
  intro er es alloc hregs a L hr hQ coefficients alphabet hR hcard hcounter hbits h111 hout hnL
  have hN' : DyadicSchedule.N k T n ≤ n := by simpa only [pow_one] using hN
  have hNL : DyadicSchedule.N k T n ≤ L := hN'.trans hnL
  have hb := Subexp.LocalBasisBatchScheduleBounds.block_bounds k T n hn
  exact executionBound_le_runtime alloc hregs a (p n) hr hQ coefficients alphabet
    factor C d L n hcounter (hR.le.trans (hb.degree_le.trans hNL))
    (hb.color_le.trans hNL) (hb.position_le.trans hNL) hbits h111 hout
    (hnative hr hQ coefficients alphabet hR hcard)

end SubexponentialSAT.SubexpMainLocalBasis

end OAI.Algorithms
