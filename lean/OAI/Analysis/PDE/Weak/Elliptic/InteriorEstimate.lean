import OAI.Analysis.PDE.Weak.Elliptic.CutoffTest

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Interior difference-quotient estimate for the actual divergence-form
equation.  All constants are independent of the nonzero difference step. -/
theorem interior_difference_energy_of_admissible
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : Continuous A) {lam Λ D K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD0 : 0 ≤ D) (hK0 : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hweak : WeakDivergenceEquation Ω
      (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (j : Fin (m + 1)) {h : ℝ} (hh : h ≠ 0)
    (hDA : ∀ x, ‖differenceQuotient (Pi.single j 1) h A x‖ ≤ D)
    {Ωtest : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hadmissible :
      let q := cutoffH1Pair η (hη.of_le (by simp)) hηM hηK
        (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK
          (differenceH1Pair (Pi.single j 1) h p))
      q ∈ H1Zero Ωtest ∧ differenceH1Pair (Pi.single j 1) (-h) q ∈ H1Zero Ω) :
    ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume (Pi.single j 1) h p.2)‖ ^ 2 ≤
      ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
        4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam := by
  let v : OAI.Analysis.PDE.Variational.CellCoordinates m := Pi.single j 1
  let T := cutoffL2 (V := OAI.Analysis.PDE.Variational.CellVectors m) (μ := volume) η hη.continuous hηM
  let W := vectorProductL2 (μ := volume) (OAI.Analysis.PDE.Variational.cellGradient η)
    (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp))) hηK
  let B := fieldMultiplierCLM (μ := volume) (fun x ↦ A (x + h • v))
    (hA.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ hAM (x + h • v))
  let R := fieldMultiplierCLM (differenceQuotient v h A)
    (continuous_differenceQuotient v h hA).aestronglyMeasurable
    (Eventually.of_forall hDA) p.2
  let P := T (differenceQuotientL2 volume v h p.2)
  let U := W (differenceQuotientL2 volume v h p.1)
  let q := cutoffH1Pair η (hη.of_le (by simp)) hηM hηK
    (cutoffH1Pair η (hη.of_le (by simp)) hηM hηK (differenceH1Pair v h p))
  have hq := hadmissible
  have hQ : q.2 = T (P + (2 : ℝ) • U) :=
    cutoffH1Pair_twice_gradient η (hη.of_le (by simp)) hηM hηK (differenceH1Pair v h p)
  have hQn : ‖q.2‖ ≤ ‖P‖ + 2 * ‖U‖ :=
    cutoffH1Pair_twice_gradient_norm η (hη.of_le (by simp)) hηM hηK (differenceH1Pair v h p)
  have hBn : ‖B‖ ≤ Λ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hΛ
    intro z
    exact norm_fieldMultiplier_le (fun x ↦ A (x + h • v))
      (hA.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ hAM (x + h • v)) z
  have hBe : lam * ‖P‖ ^ 2 ≤ inner ℝ (B P) P :=
    fieldMultiplier_lower_bound _ _ _ (Eventually.of_forall fun x ↦ hell (x + h • v)) P
  have hid : inner ℝ
      (differenceQuotientL2 volume v h
        (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hAM) p.2)) q.2 =
      inner ℝ (B P) (P + (2 : ℝ) • U) + inner ℝ R q.2 := by
    rw [differenceQuotientL2_fieldMultiplier v h A hA hAM hDA, inner_add_left]
    congr 1
    rw [hQ, inner_cutoffL2, cutoffL2_fieldMultiplier]
  have he := hweak.shifted_h1Zero_test_bound j hh hq.1 hq.2
  change |inner ℝ (differenceQuotientL2 volume v h _) q.2| ≤ ‖f‖ * ‖q.2‖ at he
  rw [hid] at he
  have hraw := coercive_cutoff_energy_bound B P U q.2 R hlam hΛ (norm_nonneg f) hBn hBe hQn he
  have hUn : ‖U‖ ≤ K * ‖p.2‖ := by
    exact (norm_vectorProductL2_le _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (OAI.Analysis.PDE.Weak.H1Zero.difference_bound hp j hh) hK0)
  have hRn : ‖R‖ ≤ D * ‖p.2‖ := norm_fieldMultiplier_le (differenceQuotient v h A)
    (continuous_differenceQuotient v h hA).aestronglyMeasurable
    (Eventually.of_forall hDA) p.2
  have hsum : ‖f‖ + ‖R‖ + 2 * Λ * ‖U‖ ≤
      ‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hUn (show 0 ≤ 2 * Λ by positivity)]
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  have hprod : 4 * (‖f‖ + ‖R‖) * ‖U‖ ≤
      4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖) := by
    exact mul_le_mul (by linarith) hUn (norm_nonneg _)
      (by positivity)
  exact hraw.trans (div_le_div_of_nonneg_right
    (add_le_add (div_le_div_of_nonneg_right hsq hlam.le) hprod) hlam.le)

theorem interior_difference_energy
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : Continuous A) {lam Λ D K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD0 : 0 ≤ D) (hK0 : 0 ≤ K)
    (hAM : ∀ x, ‖A x‖ ≤ Λ)
    (hell : ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z)
    (p : H1Pair m) (hp : p ∈ H1Zero univ)
    (f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hweak : WeakDivergenceEquation Ω
      (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hAM) p.2) f)
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηM : ∀ x, |η x| ≤ 1) (hηK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (j : Fin (m + 1)) {h : ℝ} (hh : h ≠ 0)
    (hDA : ∀ x, ‖differenceQuotient (Pi.single j 1) h A x‖ ≤ D)
    (hsub : tsupport η ⊆ Ω)
    (hshift : (fun x ↦ x + (-h) • Pi.single j 1) ⁻¹' tsupport η ⊆ Ω) :
    ‖cutoffL2 η hη.continuous hηM
      (differenceQuotientL2 volume (Pi.single j 1) h p.2)‖ ^ 2 ≤
      ((‖f‖ + D * ‖p.2‖ + 2 * Λ * (K * ‖p.2‖)) ^ 2 / lam +
        4 * (‖f‖ + D * ‖p.2‖) * (K * ‖p.2‖)) / lam := by
  exact interior_difference_energy_of_admissible A hA hlam hΛ hD0 hK0 hAM hell
    p hp f hweak η hη hηM hηK j hh hDA
    (OAI.Analysis.PDE.Weak.H1Zero.cutoff_difference_test hp η hη hηM hηK (Pi.single j 1) h hsub hshift)

end OAI.Analysis.PDE.Weak
