import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorMetric

/-! # Covector Pair -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorPair.CM.Construction

noncomputable section

/-! The real part of the intrinsic Hermitian covector pairing is the
sum of the metric-dual pairings of the real and imaginary components. -/

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem covectorInner_re_riesz (q r : F →L[ℝ] ℂ) :
    (Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner q.toLinearMap r.toLinearMap).re =
      inner ℝ ((InnerProductSpace.toDual ℝ F).symm (Complex.reCLM.comp q))
        ((InnerProductSpace.toDual ℝ F).symm (Complex.reCLM.comp r)) +
      inner ℝ ((InnerProductSpace.toDual ℝ F).symm (Complex.imCLM.comp q))
        ((InnerProductSpace.toDual ℝ F).symm (Complex.imCLM.comp r)) := by
  let b := stdOrthonormalBasis ℝ F
  have hcomp (P : ℂ →L[ℝ] ℝ) (f : F →L[ℝ] ℂ) :
      Metric.CM.Construction.complexGradientComponent b P (GlobalLp.CM.Construction.complexCovectorComponents b f) =
        (InnerProductSpace.toDual ℝ F).symm (P.comp f) := by
    rw [CovectorMetric.CM.Construction.complexGradientComponent_eq_riesz, GlobalLp.CM.Construction.complexCovectorSynthesis_components]
  rw [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_eq_basis b, ← hcomp Complex.reCLM q, ← hcomp Complex.reCLM r,
    ← hcomp Complex.imCLM q, ← hcomp Complex.imCLM r, Metric.CM.Construction.complexGradientComponent_inner,
    Metric.CM.Construction.complexGradientComponent_inner, ← Finset.sum_add_distrib]
  simp only [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (star (q (b i)) * r (b i)).re = (q (b i)).re * (r (b i)).re + (q (b i)).im * (r (b i)).im
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem metricDualVector_into_inner (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (T : E ≃L[ℝ] F)
    (hT : ∀ x y : E, B x y = inner ℝ (T x) (T y)) (q : F →L[ℝ] ℝ) :
    T (CovectorMetric.CM.Construction.metricDualVector B (q.comp T.toContinuousLinearMap)) = (InnerProductSpace.toDual ℝ F).symm q := by
  apply ext_inner_right ℝ
  intro w
  obtain ⟨v, rfl⟩ := T.surjective w
  rw [← hT, CovectorMetric.CM.Construction.metricDualVector_spec B hB, InnerProductSpace.toDual_symm_apply]
  rfl

theorem covectorMetric_into_inner (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (T : E ≃L[ℝ] F)
    (hT : ∀ x y : E, B x y = inner ℝ (T x) (T y)) (q r : F →L[ℝ] ℝ) :
    CovectorMetric.CM.Construction.covectorMetric B (q.comp T.toContinuousLinearMap) (r.comp T.toContinuousLinearMap) =
      inner ℝ ((InnerProductSpace.toDual ℝ F).symm q) ((InnerProductSpace.toDual ℝ F).symm r) := by
  change r (T (CovectorMetric.CM.Construction.metricDualVector B (q.comp T.toContinuousLinearMap))) = _
  rw [metricDualVector_into_inner B hB T hT, real_inner_comm, InnerProductSpace.toDual_symm_apply]

theorem covectorInner_re_metric_pullback (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (T : E ≃L[ℝ] F)
    (hT : ∀ x y : E, B x y = inner ℝ (T x) (T y)) (q r : F →L[ℝ] ℂ) :
    (Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner q.toLinearMap r.toLinearMap).re =
      CovectorMetric.CM.Construction.covectorMetric B (Complex.reCLM.comp (q.comp T.toContinuousLinearMap))
        (Complex.reCLM.comp (r.comp T.toContinuousLinearMap)) +
      CovectorMetric.CM.Construction.covectorMetric B (Complex.imCLM.comp (q.comp T.toContinuousLinearMap))
        (Complex.imCLM.comp (r.comp T.toContinuousLinearMap)) := by
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [covectorMetric_into_inner B hB T hT, covectorMetric_into_inner B hB T hT]
  exact covectorInner_re_riesz q r

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorPair.CM.Construction
