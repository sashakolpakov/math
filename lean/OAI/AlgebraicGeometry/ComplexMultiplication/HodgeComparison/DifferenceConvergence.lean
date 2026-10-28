import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpDominated

/-! # Difference Convergence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence.CM.Construction

noncomputable section

/-! Strong convergence of genuine spatial difference quotients to weak
derivatives, needed when differentiating a weak elliptic equation. -/

open _root_.MeasureTheory FourierTransform Filter
open scoped SchwartzMap _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sobolevL2Embedding_fourier_coe {s : ℝ} (hs : 0 ≤ s) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (SobolevIs.CM.Construction.sobolevL2Embedding hs u) : Lp ℂ 2 volume) x =
      (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) * (𝓕 u : Lp ℂ 2 volume) x :=
  LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (SobolevIs.CM.Construction.negative_besselSymbol_bound hs) u _
    (SobolevIs.CM.Construction.sobolevL2Embedding_distribution hs u)

theorem sobolevL2Derivative_fourier_coe (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp ℂ 2 volume) x =
      (DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) *
        (𝓕 u : Lp ℂ 2 volume) x := by
  let κ : ℂ := 2 * Real.pi * Complex.I
  let M := SobolevIs.CM.Construction.l2FourierMultiplier (F := ℂ) (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m)
  have hEq : 𝓕 (SobolevDifferential.CM.Construction.sobolevL2Derivative m u) = κ • 𝓕 (M u) :=
    (Lp.fourierTransformₗᵢ E ℂ).map_smul κ (M u)
  have hM : ∀ᵐ x ∂(volume : Measure E), (𝓕 (M u) : Lp ℂ 2 volume) x =
      Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) * (𝓕 u : Lp ℂ 2 volume) x :=
    LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) u (M u)
      (SobolevIs.CM.Construction.l2FourierMultiplier_distribution (by fun_prop) (Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) u)
  rw [hEq]
  filter_upwards [Lp.coeFn_smul κ (𝓕 (M u)), hM] with x hx hm
  simp only [hx, hm, Pi.smul_apply, smul_eq_mul, κ, DifferenceCriterion.CM.Construction.fourierDerivativeSymbol, Complex.ofReal_mul,
    Complex.ofReal_ofNat, real_inner_comm m x]
  ring

/-- Difference quotients converge in L2 to the actual weak derivative of
the H1 function specified by its Bessel coordinate. -/
theorem l2DifferenceQuotient_tendsto_derivative (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)) (𝓝[≠] 0)
      (𝓝 (SobolevDifferential.CM.Construction.sobolevL2Derivative m u)) := by
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  let q : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)
  let c : ℝ := 2 * Real.pi * ‖m‖
  let f : ℝ → E → ℂ := fun t x => (DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x) * (𝓕 u : Lp ℂ 2 volume) x
  let f₀ : E → ℂ := fun x => (DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x) * (𝓕 u : Lp ℂ 2 volume) x
  have hcoef (x : E) : Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x)
      (𝓝[≠] 0) (𝓝 (DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x)) :=
    (DifferenceQuotients.CM.Construction.differenceQuotientSymbol_tendsto (inner ℝ m x)).mul_const (q x)
  have hcoefBound (x : E) : ‖DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x‖ ≤ c :=
    le_of_tendsto (hcoef x).norm (Filter.Eventually.of_forall (fun t => DifferenceBounds.CM.Construction.differenceQuotient_bessel_bound m x t))
  have hF (t : ℝ) : (𝓕 (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (J u)) : Lp ℂ 2 volume) =ᵐ[volume] f t := by
    filter_upwards [DifferenceQuotients.CM.Construction.fourier_l2DifferenceQuotient_coe m t (J u),
      sobolevL2Embedding_fourier_coe (by norm_num : (0 : ℝ) ≤ 1) u] with x hd hJ
    rw [hd, hJ]
    exact (mul_assoc _ _ _).symm
  have hlim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun t : ℝ => f t x) (𝓝[≠] 0) (𝓝 (f₀ x)) :=
    Filter.Eventually.of_forall (fun x => (hcoef x).mul_const _)
  have hb : MemLp (fun x => c * ‖(𝓕 u : Lp ℂ 2 volume) x‖) 2 (volume : Measure E) :=
    (Lp.memLp (𝓕 u : Lp ℂ 2 volume)).norm.const_smul c
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂(volume : Measure E),
      ‖f t x‖ ≤ c * ‖(𝓕 u : Lp ℂ 2 volume) x‖ :=
    Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun x => by
      change ‖(DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x) * (𝓕 u : Lp ℂ 2 volume) x‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (DifferenceBounds.CM.Construction.differenceQuotient_bessel_bound m x t) (norm_nonneg _)))
  have hbound₀ : ∀ᵐ x ∂(volume : Measure E), ‖f₀ x‖ ≤ c * ‖(𝓕 u : Lp ℂ 2 volume) x‖ :=
    Filter.Eventually.of_forall (fun x => by
      change ‖(DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x) * (𝓕 u : Lp ℂ 2 volume) x‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcoefBound x) (norm_nonneg _))
  have hfourier := LpDominated.CM.Construction.l2_tendsto_dominated_representatives
    (fun t : ℝ => (𝓕 (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (J u)) : Lp ℂ 2 volume))
    (𝓕 (SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp ℂ 2 volume) f f₀ hF
    (sobolevL2Derivative_fourier_coe m u) _ hb hbound hbound₀ hlim
  have h := (Lp.fourierTransformₗᵢ E ℂ).symm.continuous.tendsto _ |>.comp hfourier
  have hInv (w : Lp ℂ 2 (volume : Measure E)) : (Lp.fourierTransformₗᵢ E ℂ).symm (𝓕 w) = w :=
    (Lp.fourierTransformₗᵢ E ℂ).symm_apply_apply w
  simpa only [Function.comp_def, hInv] using h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence.CM.Construction
