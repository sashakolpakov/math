import OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian

/-! # Real Fresnel Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.RealFresnelNormalization.Construction

noncomputable section

section

/-! Real Fresnel pairing by dominated convergence of Gaussian cutoffs. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

def realTensorDamping (n : ℕ) (c ε : ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) : ℂ :=
  ∏ i, RealDiagonalGaussian.Construction.realQuadraticDamping c ε (x i)

theorem realTensorDamping_integrable (n : ℕ) (c ε : ℝ) (hε : 0 < ε) :
    Integrable (Construction.realTensorDamping n c ε) :=
  Integrable.fintype_prod (fun _ => RealDiagonalGaussian.Construction.realQuadraticDamping_integrable c ε hε)

theorem realTensorDamping_norm_le {n : ℕ} (c ε : ℝ) (hε : 0 ≤ ε) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    ‖Construction.realTensorDamping n c ε x‖ ≤ 1 := by
  rw [Construction.realTensorDamping, norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => RealDiagonalGaussian.Construction.realQuadraticDamping_norm_le c ε (x i) hε)

theorem realTensorDamping_tendsto {n : ℕ} (c : ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    Tendsto (fun ε => Construction.realTensorDamping n c ε x) (𝓝[>] (0 : ℝ))
      (𝓝 (Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic 1 x))) := by
  have h := tendsto_finsetProd Finset.univ (fun (i : Fin n) _ => RealDiagonalGaussian.Construction.realQuadraticDamping_tendsto c (x i))
  simpa only [Construction.realTensorDamping, ← CompactCharacter.Construction.character_finset_sum, ← FresnelLimit.Construction.quadratic_one_sum] using! h

theorem fourier_realTensorDamping {n : ℕ} (c ε : ℝ) (hε : 0 < ε) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (Construction.realTensorDamping n c ε) x =
      Gaussian.Construction.realDampedGaussian c 1 ε ^ n *
        ∏ i, Complex.exp (-((Real.pi : ℂ) ^ 2 * c ^ 2 * (x i) ^ 2) /
          ((ε : ℂ) - Real.pi * c * Complex.I)) := by
  rw [show (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n)) = Measure.pi (fun _ : Fin n => (volume : Measure ℝ)) from rfl]
  unfold Construction.realTensorDamping
  rw [FourierTensor.Construction.fourierIntegral_product]
  simp only [RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping c ε hε, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem fourier_realTensorDamping_tendsto {n : ℕ} (c : ℝ) (hc : c ≠ 0) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    Tendsto (fun ε => FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (Construction.realTensorDamping n c ε) x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) ^ n * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x))) := by
  have h := tendsto_finsetProd Finset.univ
    (fun (i : Fin n) _ => RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping_tendsto c hc (x i))
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← CompactCharacter.Construction.character_finset_sum, Finset.sum_neg_distrib, ← FresnelLimit.Construction.quadratic_one_sum] at h
  convert h using 1
  funext ε
  exact FourierTensor.Construction.fourierIntegral_product (Gaussian.Construction.realCharacter c) volume (fun _ => RealDiagonalGaussian.Construction.realQuadraticDamping c ε) x

theorem fourier_realTensorDamping_norm_le {n : ℕ} (c ε : ℝ) (hε : 0 < ε) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    ‖FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (Construction.realTensorDamping n c ε) x‖ ≤
      ‖Gaussian.Construction.realDampedGaussian c 1 ε‖ ^ n := by
  rw [fourier_realTensorDamping c ε hε, norm_mul, norm_pow]
  apply mul_le_of_le_one_right (by positivity)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun i _ => RealDiagonalGaussian.Construction.realFresnelGaussian_factor_norm_le c ε (x i) hε.le)

theorem real_fresnel_pairing_volume {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    {f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ} (hf : Integrable f)
    (hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f)) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x * Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic 1 x)) =
      ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) ^ n *
        ∫ x, f x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) := by
  have hχ : Continuous (fun t => Gaussian.Construction.realCharacter c t) := (RealTestSpace.Construction.realCharacter_temperate c).1.continuous
  let d : ℂ := (Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)
  have hleft : Tendsto (fun ε : ℝ => ∫ x,
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x * Construction.realTensorDamping n c ε x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x * Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic 1 x))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x‖)
    · exact Eventually.of_forall fun ε => hF.aestronglyMeasurable.mul
        ((by unfold Construction.realTensorDamping; simp_rw [RealDiagonalGaussian.Construction.realQuadraticDamping_eq]; fun_prop :
          Continuous (realTensorDamping n c ε)).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (realTensorDamping_norm_le c ε hε.le x)
    · exact hF.norm
    · exact Eventually.of_forall fun x => (realTensorDamping_tendsto c x).const_mul _
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖Gaussian.Construction.realDampedGaussian c 1 ε‖ ≤ ‖d‖ + 1 :=
    (RealDiagonalGaussian.Construction.realDampedGaussian_tendsto c hc).norm.eventually_le_const (lt_add_one _)
  have hright : Tendsto (fun ε : ℝ => ∫ x,
      f x * FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (Construction.realTensorDamping n c ε) x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, f x * (d ^ n * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x)))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ * (‖d‖ + 1) ^ n)
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
      apply hf.aestronglyMeasurable.mul
      exact (FourierTools.Construction.fourierIntegral_continuous (Gaussian.Construction.realCharacter c) (QuadraticIntertwiner.Construction.realCharacter_unitary c) hχ volume
        (realTensorDamping_integrable n c ε hε)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0), hbound] with ε hε hb
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((fourier_realTensorDamping_norm_le c ε hε x).trans (pow_le_pow_left₀ (norm_nonneg _) hb n))
          (norm_nonneg _)
    · exact hf.norm.mul_const _
    · exact Eventually.of_forall fun x => (fourier_realTensorDamping_tendsto c hc x).const_mul _
  have heq := hleft.congr' (show (fun ε : ℝ => ∫ x,
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x * Construction.realTensorDamping n c ε x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ∫ x, f x * FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (Construction.realTensorDamping n c ε) x) from by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    exact FresnelLimit.Construction.fourierIntegral_mul_swap (Gaussian.Construction.realCharacter c) (QuadraticIntertwiner.Construction.realCharacter_unitary c) hχ volume hf
      (realTensorDamping_integrable n c ε hε))
  have h := tendsto_nhds_unique heq hright
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp [d]; ring

end

/-! The Fresnel coefficient equals the actual normalized real Gaussian index. -/

open _root_.MeasureTheory

theorem realGaussian_coefficient_normalized (c : ℝ) (hc : c ≠ 0) :
    (Real.sqrt |c| : ℂ) * (Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ) =
      FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 := by
  let d : ℂ := (Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)
  have hsquare : d ^ (2 : ℕ) = Complex.I / (c : ℂ) := by simp [d, one_div]
  have hnorm : ‖d‖ ^ 2 = 1 / |c| := by
    simpa only [norm_pow, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs] using congrArg norm hsquare
  have hprod : (Real.sqrt |c| * ‖d‖) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), hnorm, mul_one_div_cancel (abs_ne_zero.mpr hc)]
  have hunit : Real.sqrt |c| * ‖d‖ = 1 := by
    have hpos : 0 ≤ Real.sqrt |c| * ‖d‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith
  have hd : ‖d‖ ≠ 0 := by intro hz; rw [hz, mul_zero] at hunit; exact zero_ne_one hunit
  rw [Gaussian.Construction.gaussianIndex_real_eq c 1 hc one_ne_zero]
  simp only [Complex.ofReal_one, mul_one]
  change (Real.sqrt |c| : ℂ) * d = d / (‖d‖ : ℂ)
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hd)).mpr
  have hu : (Real.sqrt |c| : ℂ) * (‖d‖ : ℂ) = 1 := by exact_mod_cast hunit
  calc
    _ = ((Real.sqrt |c| : ℂ) * (‖d‖ : ℂ)) * d := by ring
    _ = d := by rw [hu, one_mul]

theorem real_fresnel_pairing {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val x *
      Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) =
      FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n *
        ∫ x, f.val x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c) := by
  have hf : Integrable f.val := FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume f
  have hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f.val) := by
    have h := FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume
      ((FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv (RealFourierFamily.Construction.realFrequencyAddEquiv n c hc)) (RealFourierLp.Construction.realBruhatFourier n f))
    convert! h using 1
    funext x
    rw [RealNormalization.Construction.real_fourier_frequency, ← RealFourierLp.Construction.realBruhatFourier_apply]
    rfl
  have hp := real_fresnel_pairing_volume c hc hf hF
  have hcoef : (Real.sqrt |c| ^ n : ℂ) * ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) ^ n =
      FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n := by
    rw [← mul_pow, realGaussian_coefficient_normalized c hc]
  simp_rw [RealNormalization.Construction.fourierIntegral_real_normalized c hc, Complex.real_smul]
  rw [RealNormalization.Construction.positionMeasure_real n c hc, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul, mul_assoc, integral_const_mul]
  rw [hp]
  push_cast
  calc
    _ = ((Real.sqrt |c| : ℂ) ^ n * ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) ^ n) *
        ((Real.sqrt |c| : ℂ) ^ n * ∫ x, f.val x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x)) := by ring
    _ = _ := by rw [hcoef]

end

end OAI.RepresentationTheory.Weil.Local.RealFresnelNormalization.Construction
