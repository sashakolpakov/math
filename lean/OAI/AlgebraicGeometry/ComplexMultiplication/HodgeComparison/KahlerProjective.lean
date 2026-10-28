import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OrthonormalKahlerForm
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicChartPair

/-! # Kahler Projective -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerProjective.CM.Construction

noncomputable section

section

/-! The actual exterior metric pairs the Kähler top power positively
with i α ∧ conjugate(α) times the penultimate power. -/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem formMetricPair_self_pos (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ha : a ≠ 0) :
    0 < (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a a).re := by
  apply lt_of_le_of_ne (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n a)
  intro hz
  apply ha
  apply Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_definite n a
  rw [← Analysis.HodgeTheory.Decomposition.Form.Constructions.formMetricPair_self_re, ← hz]
  rfl

theorem formMetricPair_real_smul (n : ℕ) (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r s : ℝ) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (r • a) (s • b) = ((r * s : ℝ) : ℂ) * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a b := by
  have hr : r • a = (r : ℂ) • a := by
    ext v
    exact Complex.real_smul
  have hs : s • b = (s : ℂ) • b := by
    ext v
    exact Complex.real_smul
  rw [hr, hs, Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions.formMetricPair_smul_left, Analysis.HodgeTheory.Decomposition.UnitaryTypes.Constructions.formMetricPair_smul_right]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, mul_assoc]

variable [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]

def kahlerTopMetricPair (n : ℕ) (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : E →L[ℂ] ℂ) : ℂ :=
  Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair ((n + 1) + (n + 1)) (CovectorProduct.CM.Construction.covectorTwoProduct (n + 1) (fun _ => f))
    (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega)
      (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorProduct.CM.Construction.covectorTwoProduct n (fun _ => f)) (Powers.CM.Construction.holomorphicRankOneForm a)))

theorem kahlerTopMetricPair_coframe (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) :
    ∃ r : ℝ, 0 < r ∧ kahlerTopMetricPair n (CovectorProduct.CM.Construction.coframeKahlerForm b.toBasis) a =
      ((r * CovectorProduct.CM.Construction.mixedCoframeCoefficient b.toBasis a : ℝ) : ℂ) *
        Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair ((n + 1) + (n + 1))
          (CovectorProduct.CM.Construction.holomorphicRankOneProduct (n + 1) (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis))
          (CovectorProduct.CM.Construction.holomorphicRankOneProduct (n + 1) (CovectorProduct.CM.Construction.basisHolomorphicCovector b.toBasis)) := by
  obtain ⟨r, hr, he⟩ := CovectorProduct.CM.Construction.coframeKahlerForm_top_positive_multiple b.toBasis
  refine ⟨r, hr, ?_⟩
  unfold kahlerTopMetricPair
  rw [he, CovectorProduct.CM.Construction.coframeKahlerForm_mixed_power, formMetricPair_real_smul]

theorem kahlerTopMetricPair_nonneg (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ E)
    (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hr : ∀ v, (f v).im = 0)
    (hg : ∀ u v, KahlerDifferential.CM.Construction.metricFromTwoForm f u v = ⟪u, v⟫_ℝ) (a : E →L[ℂ] ℂ) :
    0 ≤ (kahlerTopMetricPair n f a).re := by
  rw [OrthonormalKahlerForm.CM.Construction.real_metric_twoForm_eq_coframe b f hr hg]
  obtain ⟨r, hr, he⟩ := kahlerTopMetricPair_coframe n b a
  rw [he, Complex.re_ofReal_mul]
  exact mul_nonneg (mul_nonneg hr.le (CovectorProduct.CM.Construction.mixedCoframeCoefficient_nonneg b.toBasis a))
    (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg _ _)

theorem kahlerTopMetricPair_pos (n : ℕ) (b : OrthonormalBasis (Fin (n + 1)) ℂ E)
    (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hr : ∀ v, (f v).im = 0)
    (hg : ∀ u v, KahlerDifferential.CM.Construction.metricFromTwoForm f u v = ⟪u, v⟫_ℝ) (a : E →L[ℂ] ℂ) (ha : a ≠ 0) :
    0 < (kahlerTopMetricPair n f a).re := by
  rw [OrthonormalKahlerForm.CM.Construction.real_metric_twoForm_eq_coframe b f hr hg]
  obtain ⟨r, hr, he⟩ := kahlerTopMetricPair_coframe n b a
  rw [he, Complex.re_ofReal_mul]
  exact mul_pos (mul_pos hr (CovectorProduct.CM.Construction.mixedCoframeCoefficient_pos b.toBasis a ha))
    (formMetricPair_self_pos _ _ (CovectorProduct.CM.Construction.basisRankOneProduct_ne_zero b.toBasis))

end

section

/-! The constructed Fubini–Study powers and mixed top forms have the
actual exterior-power expressions in every manifold chart. -/

open scoped _root_.Manifold ContDiff

theorem fubiniStudyPower_inChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (k : ℕ) (y : V.analyticModel) :
    (Powers.CM.Construction.fubiniStudyPower V k).val.val.inChart e y =
      CovectorProduct.CM.Construction.covectorTwoProduct k (fun _ => (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val.inChart e y) := by
  induction k with
  | zero =>
      ext v
      have hv : v = 0 := by ext i; exact Fin.elim0 i
      rw [hv]
      change (NormalizedPrimitives.CM.Construction.constantZeroForm V.analyticModel V.analyticSpace 1).val.inChart e y 0 = 1
      rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero_apply]
      exact NormalizedPrimitives.CM.Construction.constantZeroForm_scalar V.analyticModel V.analyticSpace 1 _
  | succ k ih =>
      change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast _
        (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Powers.CM.Construction.fubiniStudyPower V k).val.val (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val)).inChart e y = _
      rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart]
      change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast _ (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge ((Powers.CM.Construction.fubiniStudyPower V k).val.val.inChart e y) _) = _
      rw [ih]
      rfl

def fubiniStudyMixedTop (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace ((k + 1) + (k + 1)) :=
  AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast (by omega)
    (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (Powers.CM.Construction.fubiniStudyPower V k)
      (Complex.I • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a (Conjugation.CM.Construction.conjugateClosedForm a)))

theorem fubiniStudyMixedTop_inChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) (y : V.analyticModel)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 (a.val.val.inChart e y)) :
    (fubiniStudyMixedTop V k a).val.val.inChart e y =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega)
        (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorProduct.CM.Construction.covectorTwoProduct k (fun _ => (IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val.inChart e y))
          (Powers.CM.Construction.holomorphicRankOneForm (PureOneCovector.CM.Construction.holomorphicOneCovector (a.val.val.inChart e y) ha))) := by
  change (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast _
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge (Powers.CM.Construction.fubiniStudyPower V k).val.val
      (Complex.I • AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.val.val (Conjugation.CM.Construction.conjugateRawForm a.val.val)))).inChart e y = _
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldDegreeCast_inChart, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, Conjugation.CM.Construction.conjugateRawForm_inChart]
  change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast _ (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge ((Powers.CM.Construction.fubiniStudyPower V k).val.val.inChart e y)
    (Complex.I • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a.val.val.inChart e y)
      (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (a.val.val.inChart e y)))) = _
  rw [fubiniStudyPower_inChart]
  unfold Powers.CM.Construction.holomorphicRankOneForm
  rw [PureOneCovector.CM.Construction.holomorphicOneCovector_reconstruct]

end

section

/-! The actual projective Kähler powers in the genuine metric fiber. -/

open scoped _root_.Manifold InnerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (y : V.analyticModel) (hy : y ∈ e.target)

def projectiveMetricKahlerCovector : Analysis.DifferentialForms.Manifold.Basic.FormValue (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) 2 :=
  Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy 2 ((IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V).val.inChart e y)

theorem projectiveMetricKahlerCovector_real (v : Fin 2 → Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) :
    (projectiveMetricKahlerCovector V e he y hy v).im = 0 :=
  VarietyMetric.CM.Construction.varietyFubiniStudyForm_real_inChart V e he hy
    (fun i => Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy (v i))

theorem projectiveMetricKahlerCovector_metric (u v : Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) :
    KahlerDifferential.CM.Construction.metricFromTwoForm (projectiveMetricKahlerCovector V e he y hy) u v = ⟪u, v⟫_ℝ := by
  unfold projectiveMetricKahlerCovector Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm
  rw [KahlerDifferential.CM.Construction.metricFromTwoForm_pullback]
  exact (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveMetricFiber_real_inner V e he y hy u v).symm

theorem metricCoordinateForm_fubiniStudyPower (k : ℕ) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy (k + k) ((Powers.CM.Construction.fubiniStudyPower V k).val.val.inChart e y) =
      CovectorProduct.CM.Construction.covectorTwoProduct k (fun _ => projectiveMetricKahlerCovector V e he y hy) := by
  unfold Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm
  rw [fubiniStudyPower_inChart, ← CovectorProduct.CM.Construction.covectorTwoProduct_pullback]
  rfl

theorem metricCoordinateForm_fubiniStudyMixedTop (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 (a.val.val.inChart e y)) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he y hy ((k + 1) + (k + 1))
      ((fubiniStudyMixedTop V k a).val.val.inChart e y) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega)
        (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorProduct.CM.Construction.covectorTwoProduct k (fun _ => projectiveMetricKahlerCovector V e he y hy))
          (Powers.CM.Construction.holomorphicRankOneForm (HolomorphicChartPair.CM.Construction.holomorphicMetricFiberCovector V e he y hy
            (a.val.val.inChart e y) ha))) := by
  unfold Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm
  rw [fubiniStudyMixedTop_inChart V e k a y ha, ← CovectorProduct.CM.Construction.covectorDegreeCast_pullback,
    ← AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback, ← CovectorProduct.CM.Construction.covectorTwoProduct_pullback,
    ← CovectorProduct.CM.Construction.holomorphicRankOneForm_pullback]
  rfl

theorem projectiveChartPair_mixedTop (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 (a.val.val.inChart e y)) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy ((k + 1) + (k + 1))
      ((Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val.inChart e y)
      ((fubiniStudyMixedTop V k a).val.val.inChart e y) =
      kahlerTopMetricPair k (projectiveMetricKahlerCovector V e he y hy)
        (HolomorphicChartPair.CM.Construction.holomorphicMetricFiberCovector V e he y hy (a.val.val.inChart e y) ha) := by
  unfold Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair
  rw [metricCoordinateForm_fubiniStudyPower, metricCoordinateForm_fubiniStudyMixedTop V e he y hy k a ha]
  rfl

end

/-! Positivity of the actual projective metric pairing in each chart. -/

open scoped _root_.Manifold InnerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (y : V.analyticModel) (hy : y ∈ e.target)

def projectiveMetricTopBasis (k : ℕ) (hdim : k + 1 = Module.finrank ℂ V.analyticModel) :
    OrthonormalBasis (Fin (k + 1)) ℂ (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy) :=
  (stdOrthonormalBasis ℂ (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy)).reindex
    (finCongr ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).toLinearEquiv.finrank_eq.trans hdim.symm))

theorem holomorphicMetricFiberCovector_ne_zero (a : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 a) (hne : a ≠ 0) :
    HolomorphicChartPair.CM.Construction.holomorphicMetricFiberCovector V e he y hy a ha ≠ 0 := by
  intro h
  apply hne
  rw [← PureOneCovector.CM.Construction.holomorphicOneCovector_reconstruct a ha]
  ext v
  have hv := congrArg (fun f : Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.ProjectiveMetricFiber V e he y hy →L[ℂ] ℂ =>
    f ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v 0))) h
  change PureOneCovector.CM.Construction.holomorphicOneCovector a ha (Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy
    ((Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.projectiveMetricFiberEquiv V e he y hy).symm (v 0))) = 0 at hv
  rw [ContinuousLinearEquiv.apply_symm_apply] at hv
  exact hv

theorem projectiveChartPair_mixedTop_nonneg (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 (a.val.val.inChart e y)) :
    0 ≤ (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy ((k + 1) + (k + 1))
      ((Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val.inChart e y)
      ((fubiniStudyMixedTop V k a).val.val.inChart e y)).re := by
  rw [projectiveChartPair_mixedTop V e he y hy k a ha]
  exact kahlerTopMetricPair_nonneg k (projectiveMetricTopBasis V e he y hy k hdim) _
    (projectiveMetricKahlerCovector_real V e he y hy)
    (projectiveMetricKahlerCovector_metric V e he y hy) _

theorem projectiveChartPair_mixedTop_pos (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V.analyticModel 1 0 (a.val.val.inChart e y))
    (hne : a.val.val.inChart e y ≠ 0) :
    0 < (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he y hy ((k + 1) + (k + 1))
      ((Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val.inChart e y)
      ((fubiniStudyMixedTop V k a).val.val.inChart e y)).re := by
  rw [projectiveChartPair_mixedTop V e he y hy k a ha]
  exact kahlerTopMetricPair_pos k (projectiveMetricTopBasis V e he y hy k hdim) _
    (projectiveMetricKahlerCovector_real V e he y hy)
    (projectiveMetricKahlerCovector_metric V e he y hy) _
    (holomorphicMetricFiberCovector_ne_zero V e he y hy _ ha hne)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerProjective.CM.Construction
