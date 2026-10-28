import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SchwartzGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricNormalization

/-! # Gradient Energy Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientEnergyNormalization.CM.Construction

noncomputable section

/-! Ordinary and normalized Sobolev gradient energies differ by the
explicit Fourier normalization factor, including for supported tests. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem schwartzGradient_energy_normalization
    (b : OrthonormalBasis ι ℝ E) (f g : 𝓢(E, ℂ))
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ∀ x ∈ tsupport g, ∀ u v : EuclideanSpace ℂ ι,
      inner ℝ (A x ((2 * Real.pi * Complex.I : ℂ) • u)) ((2 * Real.pi * Complex.I : ℂ) • v) =
        ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 * inner ℝ (A x u) v) :
    (∫ x, inner ℝ (A x (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b f x)) (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient b g x)) =
    ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 *
      ∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f) x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [SchwartzGradient.CM.Construction.sobolevVectorGradient_schwartz_normalization b f,
    SchwartzGradient.CM.Construction.sobolevVectorGradient_schwartz_normalization b g] with x hf hg
  by_cases hx : x ∈ tsupport g
  · rw [← hf, ← hg]
    exact hA x hx _ _
  · have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hzero : EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) x = 0 :=
      (smul_eq_zero.mp (hg.trans (SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero b g hx))).resolve_left hκ
    rw [SchwartzGradient.CM.Construction.schwartzOrdinaryGradient_zero b g hx, hzero, inner_zero_right, inner_zero_right, mul_zero]

theorem varietyComplexDirichletOperator_smul_both (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (x : EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (c : ℂ) (u v : EuclideanSpace ℂ ι) :
    inner ℝ (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b x (c • u)) (c • v) =
      ‖c‖ ^ 2 * inner ℝ (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b x u) v := by
  simp only [MetricDirichlet.CM.Construction.varietyComplexDirichletOperator, InverseMetric.CM.Construction.realBilinearOperator_apply]
  exact MetricNormalization.CM.Construction.complexGradientMetric_smul_both b _ c u v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientEnergyNormalization.CM.Construction
