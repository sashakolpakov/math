import OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian
import OAI.RepresentationTheory.Weil.Local.FourierPairingLimit

/-! # Real Diagonal Fresnel -/

namespace OAI.RepresentationTheory.Weil.Local.RealDiagonalFresnel.Construction

noncomputable section

/-! Fresnel pairing for every nonsingular real diagonal quadratic form. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem quadratic_diagonal {k : Type} [Field k] {n : ℕ}
    (a : Fin n → k) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x = ∑ i, a i * x i ^ 2 / 2 := by
  simp [FunctionsMetaplectic.Construction.quadratic, Matrix.diagonal_apply, Finset.sum_div, pow_two, mul_assoc, mul_left_comm]

def realDiagonalDamping {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (ε : ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) : ℂ :=
  ∏ i, RealDiagonalGaussian.Construction.realQuadraticDamping (c * a i) ε (x i)

def realDiagonalGaussianCoefficient {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : ℂ :=
  ∏ i, (Complex.I / ((c * a i : ℝ) : ℂ)) ^ (1 / 2 : ℂ)

theorem realDiagonalDamping_tendsto {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    Tendsto (fun ε => realDiagonalDamping c a ε x) (𝓝[>] (0 : ℝ))
      (𝓝 (Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x))) := by
  have h := tendsto_finsetProd Finset.univ (fun (i : Fin n) _ => RealDiagonalGaussian.Construction.realQuadraticDamping_tendsto (c * a i) (x i))
  simpa only [realDiagonalDamping, RealDiagonalGaussian.Construction.realCharacter_quadratic_coefficient,
    ← CompactCharacter.Construction.character_finset_sum, ← quadratic_diagonal] using! h

theorem fourier_realDiagonalDamping {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (ε : ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (realDiagonalDamping c a ε) x =
      ∏ i, FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume (RealDiagonalGaussian.Construction.realQuadraticDamping (c * a i) ε) (x i) :=
  FourierTensor.Construction.fourierIntegral_product (Gaussian.Construction.realCharacter c) volume (fun i => RealDiagonalGaussian.Construction.realQuadraticDamping (c * a i) ε) x

theorem fourier_realDiagonalDamping_tendsto {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    Tendsto (fun ε => FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (realDiagonalDamping c a ε) x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (realDiagonalGaussianCoefficient c a * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal (fun i => (a i)⁻¹)) x))) := by
  simp_rw [fourier_realDiagonalDamping]
  have h := tendsto_finsetProd Finset.univ
    (fun (i : Fin n) _ => RealDiagonalGaussian.Construction.scalarFourier_realDiagonalGaussian_tendsto c hc (a i) (ha i) (x i))
  simpa only [realDiagonalGaussianCoefficient, Finset.prod_mul_distrib, ← CompactCharacter.Construction.character_finset_sum,
    Finset.sum_neg_distrib, ← quadratic_diagonal] using! h

theorem real_diagonal_fresnel_pairing_volume {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    {f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ} (hf : Integrable f)
    (hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f)) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x * Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x)) =
      realDiagonalGaussianCoefficient c a *
        ∫ x, f x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal (fun i => (a i)⁻¹)) x) := by
  have hχ : Continuous (fun t => Gaussian.Construction.realCharacter c t) := (RealTestSpace.Construction.realCharacter_temperate c).1.continuous
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable (realDiagonalDamping c a ε) := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    exact Integrable.fintype_prod (fun i => RealDiagonalGaussian.Construction.realQuadraticDamping_integrable (c * a i) ε hε)
  have hgb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖realDiagonalDamping c a ε x‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε x
    rw [realDiagonalDamping, norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => RealDiagonalGaussian.Construction.realQuadraticDamping_norm_le (c * a i) ε (x i) hε.le)
  have ht : Tendsto (fun ε => ∏ i, Gaussian.Construction.realDampedGaussian (c * a i) 1 ε) (𝓝[>] (0 : ℝ))
      (𝓝 (realDiagonalGaussianCoefficient c a)) :=
    tendsto_finsetProd Finset.univ (fun i _ => RealDiagonalGaussian.Construction.realDampedGaussian_tendsto (c * a i) (mul_ne_zero hc (ha i)))
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖∏ i, Gaussian.Construction.realDampedGaussian (c * a i) 1 ε‖ ≤ ‖realDiagonalGaussianCoefficient c a‖ + 1 :=
    ht.norm.eventually_le_const (lt_add_one _)
  have hFb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x,
      ‖FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (realDiagonalDamping c a ε) x‖ ≤
        ‖realDiagonalGaussianCoefficient c a‖ + 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0), hb] with ε hε hεb x
    rw [fourier_realDiagonalDamping, norm_prod]
    apply le_trans _ hεb
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => RealDiagonalGaussian.Construction.scalarFourier_realDiagonalGaussian_norm_le c (a i) (ha i) ε hε (x i))
  exact FourierPairingLimit.Construction.fourier_pairing_of_dominated_cutoffs (Gaussian.Construction.realCharacter c) (QuadraticIntertwiner.Construction.realCharacter_unitary c) hχ volume
    (realDiagonalDamping c a) (fun x => Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x))
    (fun x => Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal (fun i => (a i)⁻¹)) x))
    (realDiagonalGaussianCoefficient c a) (‖realDiagonalGaussianCoefficient c a‖ + 1)
    hg hgb (realDiagonalDamping_tendsto c a) hFb (fourier_realDiagonalDamping_tendsto c hc a ha) hf hF

end

end OAI.RepresentationTheory.Weil.Local.RealDiagonalFresnel.Construction
