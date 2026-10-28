import OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity
import OAI.Analysis.HodgeTheory.Decomposition.Multiplier

/-! # Chart Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartLocalization.Constructions

noncomputable section

/-! A fixed smooth chart cutoff defines a bounded localization map from the
actual manifold form L² space to Euclidean coefficient L². -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ e.source)

def projectiveLocalizationCoefficients :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  (CoefficientLinearity.Constructions.supportedCoefficientLinear V e n).comp
    ((DifferentialForms.Manifold.Algebra.smoothManifoldFormSubmodule V.analyticModel V.analyticSpace n).subtype.comp
      (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf))

include he hs

theorem projectiveLocalization_memLp
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    MemLp (projectiveLocalizationCoefficients V e n f hf a) 2 volume :=
  CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n (isClosed_tsupport f).isCompact hs
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a) (fun x hx => by
      rw [DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction_apply, image_eq_zero_of_notMem_tsupport hx]
      exact zero_smul ℂ (a x))

def projectiveLocalizationLp :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) where
  toFun a := (projectiveLocalization_memLp V e he n f hf hs a).toLp
    (projectiveLocalizationCoefficients V e n f hf a)
  map_add' a b := by
    rw [← MemLp.toLp_add (projectiveLocalization_memLp V e he n f hf hs a)
      (projectiveLocalization_memLp V e he n f hf hs b)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun ((projectiveLocalizationCoefficients V e n f hf).map_add a b))
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (projectiveLocalization_memLp V e he n f hf hs a)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun ((projectiveLocalizationCoefficients V e n f hf).map_smul c a))

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveLocalizationLp_bound :
    ∃ C : ℝ, ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ‖projectiveLocalizationLp V e he n f hf hs a‖ ≤ C * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  obtain ⟨c, hc, hcoord⟩ := CoordinateLp.Constructions.supportedCoordinatesLp_uniform_bound V e he n (isClosed_tsupport f).isCompact hs
  obtain ⟨M, hM⟩ := Multiplier.Constructions.projective_smooth_multiplier_bound V n f hf
  let B := max M 0
  have hB : 0 ≤ B := le_max_right M 0
  have hroot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨B / Real.sqrt c, fun a => ?_⟩
  have hfa := hcoord (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a) (fun x hx => by
    rw [DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction_apply, image_eq_zero_of_notMem_tsupport hx]
    exact zero_smul ℂ (a x))
  change c * ‖projectiveLocalizationLp V e he n f hf hs a‖ ^ 2 ≤
    ‖Form.Constructions.smoothToProjectiveL2 V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)‖ ^ 2 at hfa
  have hmul : ‖Form.Constructions.smoothToProjectiveL2 V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)‖ ≤
      B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ :=
    (hM a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hle : Real.sqrt c * ‖projectiveLocalizationLp V e he n f hf hs a‖ ≤
      B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
    apply (sq_le_sq₀ (mul_nonneg hroot.le (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact hfa.trans ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr hmul)
  calc
    _ ≤ (B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖) / Real.sqrt c :=
      (le_div_iff₀ hroot).mpr (by simpa only [mul_comm (Real.sqrt c)] using hle)
    _ = (B / Real.sqrt c) * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by ring

/-- Bounded chart localization of the genuine completed manifold L² space. -/
def projectiveChartLocalization : Form.Constructions.ProjectiveL2Forms V n →L[ℂ]
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (projectiveLocalizationLp V e he n f hf hs).extendOfNorm (Form.Constructions.smoothToProjectiveL2 V n)

theorem projectiveChartLocalization_on_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    projectiveChartLocalization V e he n f hf hs (Form.Constructions.smoothToProjectiveL2 V n a) =
      projectiveLocalizationLp V e he n f hf hs a :=
  LinearMap.extendOfNorm_eq (Form.Constructions.smoothToProjectiveL2_dense V n)
    (projectiveLocalizationLp_bound V e he n f hf hs) a

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartLocalization.Constructions
