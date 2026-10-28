import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerProjective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerCohomologyFunctional

/-! # Kahler Functional Positive -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFunctionalPositive.CM.Construction

noncomputable section

/-! Strict positivity of the constructed global Kähler functional on
the actual mixed top form of a nonzero holomorphic one-form. -/

open _root_.MeasureTheory
open scoped _root_.Manifold

theorem projectivePointPair_mixedTop_nonneg (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val)
    (x : V.analyticSpace) :
    0 ≤ (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V ((k + 1) + (k + 1))
      (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val.val x).re := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
  have hx : x ∈ e.source := mem_chart_source V.analyticModel x
  exact KahlerProjective.CM.Construction.projectiveChartPair_mixedTop_nonneg V e he (e x) (e.map_source hx) k hdim a
    (ha e he (e x) (e.map_source hx))

theorem projectiveL2Pair_mixedTop_nonneg (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val) :
    0 ≤ (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1))
      (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val).re := by
  change 0 ≤ RCLike.re (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V ((k + 1) + (k + 1))
    (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val.val x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V)
  rw [← integral_re (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V _ _ _)]
  exact integral_nonneg (projectivePointPair_mixedTop_nonneg V k hdim a ha)

theorem projectiveL2Pair_mixedTop_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val) (hne : a ≠ 0) :
    0 < (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1))
      (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val).re := by
  apply lt_of_le_of_ne (projectiveL2Pair_mixedTop_nonneg V k hdim a ha)
  intro hz
  have hInt := Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_integrable V ((k + 1) + (k + 1))
    (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val
  have hrealInt := integral_re hInt
  change (∫ x, (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V ((k + 1) + (k + 1))
    (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val.val x).re
      ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V) =
    (Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1)) (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val
      (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val).re at hrealInt
  rw [← hz] at hrealInt
  have hAE := (integral_eq_zero_iff_of_nonneg
    (projectivePointPair_mixedTop_nonneg V k hdim a ha)
    (Complex.reCLM.integrable_comp hInt)).mp hrealInt
  have hAll := Measure.eq_of_ae_eq hAE
    (Complex.continuous_re.comp (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormPointPair_continuous V _ _ _)) continuous_const
  apply hne
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
  have hx : x ∈ e.source := mem_chart_source V.analyticModel x
  have hchart : a.val.val.inChart e (e x) = 0 := by
    by_contra hc
    have hp := KahlerProjective.CM.Construction.projectiveChartPair_mixedTop_pos V e he (e x) (e.map_source hx) k hdim a
      (ha e he (e x) (e.map_source hx)) hc
    have hzero := congrFun hAll x
    change (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (e x) (e.map_source hx) ((k + 1) + (k + 1))
      ((Powers.CM.Construction.fubiniStudyPower V (k + 1)).val.val.inChart e (e x))
      ((KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a).val.val.inChart e (e x))).re = 0 at hzero
    exact (ne_of_gt hp) hzero
  rw [← a.val.val.inChart_comp_chartTangentMap e he hx, hchart]
  ext v
  rfl

theorem fubiniStudyBettiFunctional_mixedTop_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val) (hne : a ≠ 0) :
    0 < (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k
      ((V.deRhamBettiIso ((k + 1) + (k + 1))).hom
        (V.deRhamClass ((k + 1) + (k + 1)) (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a)))).re := by
  rw [KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional_formClass]
  exact projectiveL2Pair_mixedTop_pos V k hdim a ha hne

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFunctionalPositive.CM.Construction
