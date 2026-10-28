import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric

/-! # Covector Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction

noncomputable section

section

/-! The inverse metric pairs genuine covectors independently of an
invertible change of coordinates. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

def metricDualVector (B : E →L[ℝ] E →L[ℝ] ℝ) (q : E →L[ℝ] ℝ) : E :=
  (InverseMetric.CM.Construction.realBilinearOperator B).inverse ((InnerProductSpace.toDual ℝ E).symm q)

theorem metricDualVector_spec (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) (q : E →L[ℝ] ℝ) (v : E) :
    B (metricDualVector B q) v = q v := by
  rw [← InverseMetric.CM.Construction.realBilinearOperator_apply]
  change inner ℝ ((InverseMetric.CM.Construction.realBilinearOperator B) ((InverseMetric.CM.Construction.realBilinearOperator B).inverse
    ((InnerProductSpace.toDual ℝ E).symm q))) v = _
  rw [(InverseMetric.CM.Construction.positive_bilinear_operator_isInvertible B hB).self_apply_inverse]
  exact InnerProductSpace.toDual_symm_apply

theorem metricDualVector_unique (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) (q : E →L[ℝ] ℝ)
    (v : E) (hv : ∀ w : E, B v w = q w) : v = metricDualVector B q := by
  by_contra hne
  have hpos := hB (v - metricDualVector B q) (sub_ne_zero.mpr hne)
  have hzero : B (v - metricDualVector B q) (v - metricDualVector B q) = 0 := by
    rw [B.map_sub v (metricDualVector B q), sub_apply, hv, metricDualVector_spec B hB, sub_self]
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

def covectorMetric (B : E →L[ℝ] E →L[ℝ] ℝ) (q r : E →L[ℝ] ℝ) : ℝ :=
  r (metricDualVector B q)

omit [ProperSpace E] in
theorem inverseBilinearForm_covectors (B : E →L[ℝ] E →L[ℝ] ℝ) (q r : E →L[ℝ] ℝ) :
    InverseMetric.CM.Construction.inverseBilinearForm B ((InnerProductSpace.toDual ℝ E).symm q)
      ((InnerProductSpace.toDual ℝ E).symm r) = covectorMetric B q r := by
  rw [InverseMetric.CM.Construction.inverseBilinearForm_apply, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rfl

theorem metricDualVector_transition (B D : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) (hD : ∀ u : E, u ≠ 0 → 0 < D u u)
    (T : E →L[ℝ] E) (hT : Function.Surjective T)
    (hBD : ∀ u v : E, B u v = D (T u) (T v)) (q : E →L[ℝ] ℝ) :
    T (metricDualVector B (q.comp T)) = metricDualVector D q := by
  apply metricDualVector_unique D hD q
  intro w
  obtain ⟨v, rfl⟩ := hT w
  rw [← hBD, metricDualVector_spec B hB]
  rfl

theorem covectorMetric_transition (B D : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) (hD : ∀ u : E, u ≠ 0 → 0 < D u u)
    (T : E →L[ℝ] E) (hT : Function.Surjective T)
    (hBD : ∀ u v : E, B u v = D (T u) (T v)) (q r : E →L[ℝ] ℝ) :
    covectorMetric B (q.comp T) (r.comp T) = covectorMetric D q r := by
  change r (T (metricDualVector B (q.comp T))) = _
  rw [metricDualVector_transition B D hB hD T hT hBD]
  rfl

end

/-! Coordinate invariance of the inverse-metric energy on complex-valued
covectors, using their actual real and imaginary components. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem complexGradientComponent_inner_synthesis (b : OrthonormalBasis ι ℝ E)
    (P : ℂ →L[ℝ] ℝ) (z : EuclideanSpace ℂ ι) (u : E) :
    inner ℝ (Metric.CM.Construction.complexGradientComponent b P z) u = P (GlobalLp.CM.Construction.complexCovectorSynthesis b z u) := by
  rw [Metric.CM.Construction.complexGradientComponent_apply, sum_inner, GlobalLp.CM.Construction.complexCovectorSynthesis_apply, map_sum]
  simp only [real_inner_smul_left, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [CompleteSpace E]

theorem complexGradientComponent_eq_riesz (b : OrthonormalBasis ι ℝ E)
    (P : ℂ →L[ℝ] ℝ) (z : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientComponent b P z =
      (InnerProductSpace.toDual ℝ E).symm (P.comp (GlobalLp.CM.Construction.complexCovectorSynthesis b z)) := by
  apply ext_inner_right ℝ
  intro u
  rw [complexGradientComponent_inner_synthesis, InnerProductSpace.toDual_symm_apply]
  rfl

theorem complexGradientMetric_inverse_covectors (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (z w : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientMetric b (InverseMetric.CM.Construction.inverseBilinearForm B) z w =
      covectorMetric B (Complex.reCLM.comp (GlobalLp.CM.Construction.complexCovectorSynthesis b z))
        (Complex.reCLM.comp (GlobalLp.CM.Construction.complexCovectorSynthesis b w)) +
      covectorMetric B (Complex.imCLM.comp (GlobalLp.CM.Construction.complexCovectorSynthesis b z))
        (Complex.imCLM.comp (GlobalLp.CM.Construction.complexCovectorSynthesis b w)) := by
  simp only [Metric.CM.Construction.complexGradientMetric_apply, complexGradientComponent_eq_riesz, inverseBilinearForm_covectors]

omit [CompleteSpace E] in
theorem complexCovectorSynthesis_pullback (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (z : EuclideanSpace ℂ ι) :
    GlobalLp.CM.Construction.complexCovectorSynthesis b (GlobalLp.CM.Construction.complexCovectorPullback b T z) = (GlobalLp.CM.Construction.complexCovectorSynthesis b z).comp T := by
  change GlobalLp.CM.Construction.complexCovectorSynthesis b (GlobalLp.CM.Construction.complexCovectorComponents b ((GlobalLp.CM.Construction.complexCovectorSynthesis b z).comp T)) = _
  exact GlobalLp.CM.Construction.complexCovectorSynthesis_components b _

variable [ProperSpace E]

theorem complexInverseMetric_transition (b : OrthonormalBasis ι ℝ E)
    (B D : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, u ≠ 0 → 0 < B u u) (hD : ∀ u : E, u ≠ 0 → 0 < D u u)
    (T : E →L[ℝ] E) (hT : Function.Surjective T)
    (hBD : ∀ u v : E, B u v = D (T u) (T v)) (z w : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientMetric b (InverseMetric.CM.Construction.inverseBilinearForm B) (GlobalLp.CM.Construction.complexCovectorPullback b T z) (GlobalLp.CM.Construction.complexCovectorPullback b T w) =
      Metric.CM.Construction.complexGradientMetric b (InverseMetric.CM.Construction.inverseBilinearForm D) z w := by
  simp only [complexGradientMetric_inverse_covectors, complexCovectorSynthesis_pullback,
    ← ContinuousLinearMap.comp_assoc]
  rw [covectorMetric_transition B D hB hD T hT hBD,
    covectorMetric_transition B D hB hD T hT hBD]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorMetric.CM.Construction
