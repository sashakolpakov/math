import OAI.Analysis.HodgeTheory.Decomposition.RealMultiplier
import OAI.Analysis.HodgeTheory.Decomposition.ChartLocalization
import OAI.Analysis.HodgeTheory.Decomposition.SupportedSchwartz
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzCoordinates

/-! # Schwartz Localization -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization.Constructions

noncomputable section

/-! Linear Schwartz localization of genuine smooth manifold forms and its
scalar H¹ Bessel coordinates. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
  (hs : tsupport f ⊆ e.source)

def projectiveRealLocalizationSchwartz :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) where
  toFun a := SupportedSchwartz.Constructions.supportedCoordinatesSchwartz V e he n (isClosed_tsupport f).isCompact hs
    (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a)
    (fun _ hx => RealMultiplier.Constructions.projectiveRealMultiplier_zero_off_support V n f hf a hx)
  map_add' a b := by
    apply DFunLike.ext
    intro z
    exact congrFun ((ChartLocalization.Constructions.projectiveLocalizationCoefficients V e n (fun x => (f x : ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp hf)).map_add a b) z
  map_smul' c a := by
    apply DFunLike.ext
    intro z
    exact congrFun ((ChartLocalization.Constructions.projectiveLocalizationCoefficients V e n (fun x => (f x : ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp hf)).map_smul c a) z

theorem projectiveRealLocalizationSchwartz_coe
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    (projectiveRealLocalizationSchwartz V e he n f hf hs a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a).val := rfl

def projectiveScalarH1Localization
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevCoordinate 1).comp
    ((SchwartzCoordinates.Constructions.schwartzOrthonormalCoordinate (EuclideanSpace.basisFun _ ℂ) j).toLinearMap.comp
      (projectiveRealLocalizationSchwartz V e he n f hf hs))

theorem projectiveScalarH1Localization_norm
    (j : Set.powersetCard (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ‖projectiveScalarH1Localization V e he n f hf hs j a‖ =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevNorm 1 (SchwartzCoordinates.Constructions.schwartzOrthonormalCoordinate (EuclideanSpace.basisFun _ ℂ) j
        (projectiveRealLocalizationSchwartz V e he n f hf hs a)) := rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.SchwartzLocalization.Constructions
