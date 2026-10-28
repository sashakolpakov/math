import OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyHolomorphic
import OAI.AlgebraicGeometry.DivisorClass.Chern.MetricCurvature

/-! # Fubini Study Positive Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyPositiveMetric

noncomputable section

section

/-! The curvature prescribed by the original normalized Chern class of the twisting bundle. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def fubiniStudyTwistCurvatureClosed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 2 :=
  Holomorphic.CurvatureD.holomorphicCurvatureChernScale⁻¹ • (-(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) • ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V)

theorem fubiniStudyTwistCurvatureClosed_normalized (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Holomorphic.CurvatureD.holomorphicCurvatureChernScale • fubiniStudyTwistCurvatureClosed V =
      -(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) • ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V := by
  rw [fubiniStudyTwistCurvatureClosed, smul_smul,
    mul_inv_cancel₀ MetricCurvature.holomorphicCurvatureChernScale_ne_zero, one_smul]

theorem fubiniStudyTwistCurvatureClosed_type (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1
      (fubiniStudyTwistCurvatureClosed V).val.val :=
  ((ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V).const_smul
    (-(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ))).const_smul Holomorphic.CurvatureD.holomorphicCurvatureChernScale⁻¹

def fubiniStudyTwistCurvatureCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ℝ :=
  2 * Real.pi * (FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℝ)

theorem fubiniStudyTwistCurvatureCoefficient_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    0 < fubiniStudyTwistCurvatureCoefficient V :=
  mul_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr (FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity_pos V))

theorem fubiniStudyTwistCurvatureClosed_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Complex.I • (fubiniStudyTwistCurvatureClosed V).val =
      (fubiniStudyTwistCurvatureCoefficient V : ℂ) • ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V := by
  change Complex.I • (Holomorphic.CurvatureD.holomorphicCurvatureChernScale⁻¹ •
    (-(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) • ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V)) = _
  rw [smul_smul, smul_smul]
  congr 1
  simp only [Holomorphic.CurvatureD.holomorphicCurvatureChernScale, inv_inv, fubiniStudyTwistCurvatureCoefficient,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  calc
    Complex.I * (2 * (Real.pi : ℂ) * Complex.I) * -(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) =
      -(2 * (Real.pi : ℂ) * (FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ)) * (Complex.I * Complex.I) := by ring
    _ = 2 * (Real.pi : ℂ) * (FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) := by rw [Complex.I_mul_I]; ring

theorem fubiniStudyTwistCurvatureClosed_imaginary (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (fubiniStudyTwistCurvatureClosed V).val =
      -(fubiniStudyTwistCurvatureClosed V).val := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star (Holomorphic.CurvatureD.holomorphicCurvatureChernScale⁻¹ *
    (-(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) * ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x v)) =
      -(Holomorphic.CurvatureD.holomorphicCurvatureChernScale⁻¹ *
        (-(FubiniStudyHolomorphic.fubiniStudyTwistMultiplicity V : ℂ) * ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x v))
  apply Complex.ext <;>
    simp [Holomorphic.CurvatureD.holomorphicCurvatureChernScale, ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_real V x v]

theorem fubiniStudyTwistCurvatureClosed_betti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (V.deRhamBettiIso 2).hom
        (V.deRhamClass 2 (Holomorphic.CurvatureD.holomorphicCurvatureChernScale • fubiniStudyTwistCurvatureClosed V)) =
      V.rationalCohomologyInclusion 2
        (Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)) := by
  rw [fubiniStudyTwistCurvatureClosed_normalized, map_smul, map_smul,
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ_comparison, FubiniStudyHolomorphic.fubiniStudyTwistUnitClass_chern, map_nsmul, map_neg,
    neg_smul, Nat.cast_smul_eq_nsmul, smul_neg]

end

/-! A positive curvature metric on the actual original holomorphic twisting bundle. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance fubiniStudyPositiveMetric_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

theorem exists_fubiniStudyTwistMetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ∃ k : HolomorphicMetric.Data.HolomorphicLineMetricData (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V),
      k.curvature = (fubiniStudyTwistCurvatureClosed V).val :=
  MetricCurvature.exists_holomorphic_metric_of_normalized_betti V
    (HolomorphicMetric.Data.holomorphicLineCanonicalMetric (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V))
    (fubiniStudyTwistCurvatureClosed V) (fubiniStudyTwistCurvatureClosed_type V)
    (fubiniStudyTwistCurvatureClosed_imaginary V) (fubiniStudyTwistCurvatureClosed_betti V)

def fubiniStudyTwistMetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    HolomorphicMetric.Data.HolomorphicLineMetricData (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) :=
  (exists_fubiniStudyTwistMetric V).choose

theorem fubiniStudyTwistMetric_curvature (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (fubiniStudyTwistMetric V).curvature = (fubiniStudyTwistCurvatureClosed V).val :=
  (exists_fubiniStudyTwistMetric V).choose_spec

theorem fubiniStudyTwistMetric_real_curvature (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Complex.I • (fubiniStudyTwistMetric V).curvature =
      (fubiniStudyTwistCurvatureCoefficient V : ℂ) • ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V := by
  rw [fubiniStudyTwistMetric_curvature, fubiniStudyTwistCurvatureClosed_real]

theorem fubiniStudyTwistMetric_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x : V.analyticSpace)
    (v : TangentSpace 𝓘(ℝ, V.analyticModel) x) (hv : v ≠ 0) :
    0 < ((Complex.I • (fubiniStudyTwistMetric V).curvature) x
      ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  rw [fubiniStudyTwistMetric_real_curvature]
  change 0 < ((fubiniStudyTwistCurvatureCoefficient V : ℂ) *
    ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    mul_pos (fubiniStudyTwistCurvatureCoefficient_pos V) (ComplexMultiplication.HodgeComparison.VarietyMetric.CM.Construction.varietyFubiniStudyForm_positive V x v hv)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyPositiveMetric
