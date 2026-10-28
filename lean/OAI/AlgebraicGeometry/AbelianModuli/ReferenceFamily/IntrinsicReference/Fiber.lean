import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.FiberInvariants
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonAction

/-! # Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Algebraization of the constructed reference Hodge comparison preserves
the original polarization and every integral CM action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
attribute [local irreducible] Models.FinePELModel.complexTestFamily Intrinsic.ChernPairing.nativePolarizationForm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)
    (b : P.domain) (z : H.compatible.neighborhood)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})

def Models.FinePELModel.nativeReferenceFiberPolarizedComparison : RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison.NativePolarizedComparison
    ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
    ((M.complexTestFamily κ f).polarized.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left) where
  periods := M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z
  hodge := M.nativeReferenceFiberComparison_isHodgeMap hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk
  integral := M.nativeReferenceFiberComparison_integral hM κ hP hκ f a H z₀ hz₀ b z
  polarization := M.nativeReferenceFiberComparison_polarization hM κ hP hκ f a H z₀ hz₀ b z

theorem Models.FinePELModel.nativeReferenceFiberPolarizedComparison_periods :
    (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).periods =
      M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z := rfl

attribute [local irreducible] Models.FinePELModel.nativeReferenceFiberComparison

theorem Models.FinePELModel.nativeReferenceFiberPolarizedComparison_action (c : NumberField.RingOfIntegers E) :
    ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).map c ≫
      (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).algebraicIso.hom =
      (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).algebraicIso.hom ≫
        ((M.complexTestFamily κ f).action.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left).map c := by
  apply (M.nativeReferenceFiberPolarizedComparison hM κ hP hκ f a H z₀ hz₀ b z hs hdegree hk).algebraicIso_action
    ((M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
    ((M.complexTestFamily κ f).action.pullback (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
  intro d v
  have he := M.nativeReferenceFiberComparison_integer hM κ hP hκ f a H z₀ hz₀ b z d v
  unfold RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
