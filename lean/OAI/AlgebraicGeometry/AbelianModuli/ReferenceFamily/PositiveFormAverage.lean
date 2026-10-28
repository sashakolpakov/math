import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormPullback
import OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative

/-! # Positive Form Average -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormAverage

noncomputable section

/-! Haar averaging preserves strict positivity and reality of actual
two-forms on a compact complex Lie group. -/

open OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology _root_.MeasureTheory
open scoped _root_.Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℂ, E) ∞ G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]

def formEvaluationReal (v : Fin 2 → E) : (E [⋀^Fin 2]→L[ℝ] ℂ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℂ v).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ))

theorem averageForms_positive (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G 2)
    (ha : ∀ (x : G) (v : TangentSpace 𝓘(ℝ, E) x), v ≠ 0 →
      0 < (a x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re)
    (x : G) (u : TangentSpace 𝓘(ℝ, E) x) (hu : u ≠ 0) :
    0 < (AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms μ a x ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]).re := by
  let L : (E [⋀^Fin 2]→L[ℝ] ℂ) →L[ℝ] ℝ :=
    formEvaluationReal (E := E) ![u, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I u]
  let f (g : G) := L (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.translatedValue a g x)
  have hf (g : G) : 0 < f g := PositiveFormPullback.positiveTwoForm_pullback a.val ha (fun y : G => g * y)
    (contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := ∞)) x (PositiveFormPullback.leftTranslation_tangent_injective g x) u hu
  have hcov := (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.translatedValue_continuous a x).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hfi : Integrable f μ := L.integrable_comp hcov
  have hsup : Function.support f = Set.univ := by
    ext g
    exact iff_true_intro (hf g).ne'
  have hp : 0 < ∫ g, f g ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun g => (hf g).le) hfi).mpr
    rw [hsup, measure_univ]
    exact zero_lt_one
  have he : L (AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms μ a x) = ∫ g, f g ∂μ :=
    (congrArg L (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.averageForms_eq_integral_pullback μ a x)).trans (L.integral_comp_comm hcov).symm
  change 0 < L (AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms μ a x)
  exact he.symm ▸ hp

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [LieGroup 𝓘(ℂ, E) ∞ G] in
theorem averageForms_real (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G 2)
    (ha : ∀ (x : G) (v : Fin 2 → TangentSpace 𝓘(ℝ, E) x), (a x v).im = 0)
    (x : G) (v : Fin 2 → TangentSpace 𝓘(ℝ, E) x) : (AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms μ a x v).im = 0 := by
  let L : (E [⋀^Fin 2]→L[ℝ] ℂ) →L[ℝ] ℝ := Complex.imCLM.comp
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℂ v).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ))
  have hcov := (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.translatedValue_continuous a x).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have he : L (AbelianVariety.Averaging.Constructions.ExteriorCohomology.averageForms μ a x) = ∫ g, L (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.translatedValue a g x) ∂μ :=
    (congrArg L (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.averageForms_eq_integral_pullback μ a x)).trans (L.integral_comp_comm hcov).symm
  have hz (g : G) : L (AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology.translatedValue a g x) = 0 := ha (g * x) _
  exact he.trans ((integral_congr_ae (ae_of_all μ hz)).trans (integral_zero G ℝ))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveFormAverage
