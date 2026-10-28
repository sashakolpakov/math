import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential

/-! # Kahler Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions

noncomputable section

/-! Complex-structure compatibility of the actual projective Kähler metric.
These are geometric identities for the constructed metric, with no assumed
cohomological splitting or primitive-solvability assertion. -/

open scoped ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

def metricIUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

/-- A real metric obtained from a pure (1,1) form is invariant under the complex structure. -/
theorem metricFromTwoForm_J_invariant (f : DifferentialForms.Manifold.Basic.FormValue E 2) (hf : DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f)
    (u v : E) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm f (Complex.I • u) (Complex.I • v) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm f u v := by
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply]
  have h := hf metricIUnit ![u, Complex.I • v]
  have hc : DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 metricIUnit = 1 := by
    simp [DifferentialForms.Manifold.Bidegree.bidegreeCharacter, metricIUnit]
  rw [hc, one_mul] at h
  apply congrArg Complex.re
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Moving the complex structure between the arguments changes its sign. -/
theorem metricFromTwoForm_J_skew (f : DifferentialForms.Manifold.Basic.FormValue E 2) (hf : DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f)
    (u v : E) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm f (Complex.I • u) v = -AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm f u (Complex.I • v) := by
  have h := metricFromTwoForm_J_invariant f hf u (Complex.I • v)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The actual projective metric preserves J in every genuine holomorphic chart. -/
theorem projectiveMetric_J_invariant (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u v : V.analyticModel) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y (Complex.I • u) (Complex.I • v) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y u v :=
  metricFromTwoForm_J_invariant _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V e he y hy) u v

theorem projectiveMetric_J_skew (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u v : V.analyticModel) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y (Complex.I • u) v =
      -AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y u (Complex.I • v) :=
  metricFromTwoForm_J_skew _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V e he y hy) u v

/-- The Hermitian pairing associated with a real bilinear metric; linear in its second argument. -/
def metricHermitianPair (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) : ℂ :=
  (B u v : ℂ) - Complex.I * (B u (Complex.I • v) : ℂ)

omit [IsScalarTower ℝ ℂ E] in
theorem metricHermitianPair_add_right (B : E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    metricHermitianPair B u (v + w) = metricHermitianPair B u v + metricHermitianPair B u w := by
  simp only [metricHermitianPair, map_add, smul_add, Complex.ofReal_add]
  ring

theorem metricHermitianPair_real_smul_right (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (r : ℝ) :
    metricHermitianPair B u (r • v) = (r : ℂ) * metricHermitianPair B u v := by
  have hJ : Complex.I • (r • v) = r • (Complex.I • v) := smul_comm _ _ _
  simp only [metricHermitianPair, hJ, map_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

omit [IsScalarTower ℝ ℂ E] in
theorem metricHermitianPair_I_right (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    metricHermitianPair B u (Complex.I • v) = Complex.I * metricHermitianPair B u v := by
  simp only [metricHermitianPair, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg, Complex.ofReal_neg]
  calc
    (B u (Complex.I • v) : ℂ) - Complex.I * -(B u v : ℂ) =
      Complex.I * (B u v : ℂ) - (Complex.I * Complex.I) * (B u (Complex.I • v) : ℂ) := by
        rw [Complex.I_mul_I]
        ring
    _ = _ := by ring

theorem metricHermitianPair_smul_right (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (z : ℂ) :
    metricHermitianPair B u (z • v) = z * metricHermitianPair B u v := by
  have hR (r : ℝ) (x : E) : (r : ℂ) • x = r • x := algebraMap_smul ℂ r x
  have hz : z • v = z.re • v + z.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [add_smul, mul_smul, hR, hR]
  rw [hz, metricHermitianPair_add_right, metricHermitianPair_real_smul_right,
    metricHermitianPair_real_smul_right, metricHermitianPair_I_right]
  rw [← mul_assoc, ← add_mul, Complex.re_add_im]

/-- The projective pairing is conjugate symmetric. -/
theorem projectiveMetricHermitian_symm (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u v : V.analyticModel) :
    metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) v u =
      star (metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u v) := by
  unfold metricHermitianPair
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hy v u,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hy v (Complex.I • u),
    projectiveMetric_J_skew V e he y hy u v]
  simp only [star_sub, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

/-- Its diagonal is exactly the positive real metric. -/
theorem projectiveMetricHermitian_self (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u : V.analyticModel) :
    metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u u =
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y u u : ℂ) := by
  have h := projectiveMetric_J_skew V e he y hy u u
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_symmetric V e he hy] at h
  have hz : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y u (Complex.I • u) = 0 := by linarith
  simp [metricHermitianPair, hz]

theorem projectiveMetricHermitian_positive (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (y : V.analyticModel) (hy : y ∈ e.target) (u : V.analyticModel) (hu : u ≠ 0) :
    0 < (metricHermitianPair (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart V e y) u u).re := by
  rw [projectiveMetricHermitian_self V e he y hy, Complex.ofReal_re]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.varietyMetricInChart_positive V e he hy u hu

end

end OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions
