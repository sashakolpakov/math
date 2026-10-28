import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity

/-! # Intrinsic Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms

noncomputable section

/-! Realize the GeometricTheta Albanese theta forms as actual smooth forms on every
native projective component, retaining the proved extension by zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem integralProjective_separated (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.toOver.left.IsSeparated := by
  refine ⟨?_⟩
  exact (CategoryTheory.Limits.terminal.comp_from V.structureMap) ▸
    (inferInstance : IsSeparated (V.structureMap ≫ CategoryTheory.Limits.terminal.from Foundations.Scheme.ProjectiveSpace.complexBase))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def thetaSmoothComponent (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount) :
    D.sphericalInputs →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (D.componentVariety hg i).analyticModel
        (D.componentVariety hg i).analyticSpace 1 := by
  let V := D.componentVariety hg i
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := integralProjective_separated V
  exact (KaehlerGluing.globalSmoothForm V.toOver).comp
    ((AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)).comp
      ((D.pel.albanesePullback hg).comp Θ))

theorem thetaSmoothComponent_zero (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount)
    (c : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : D.IsCanonicalThetaLift hg j c Θ)
    (i : Fin D.pel.componentCount) (hi : i ≠ j) (φ : D.sphericalInputs) :
    thetaSmoothComponent D hg Θ i φ = 0 := by
  let V := D.componentVariety hg i
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := integralProjective_separated V
  change KaehlerGluing.globalSmoothForm V.toOver
    (AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i) (D.pel.albanesePullback hg (Θ φ))) = 0
  exact (congrArg (KaehlerGluing.globalSmoothForm V.toOver) (hΘ.2.2 i hi φ)).trans
    (map_zero (KaehlerGluing.globalSmoothForm V.toOver))

theorem thetaSmoothComponent_pure (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (i : Fin D.pel.componentCount)
    (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (D.componentVariety hg i).analyticModel
      (D.componentVariety hg i).analyticSpace 1 0 (thetaSmoothComponent D hg Θ i φ).val := by
  let V := D.componentVariety hg i
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : V.toOver.left.IsSeparated := integralProjective_separated V
  exact OpenPurity.Kaehler.globalSmoothForm_pure V.toOver _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms
