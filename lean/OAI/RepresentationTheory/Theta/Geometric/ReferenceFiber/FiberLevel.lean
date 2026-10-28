import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.LevelPoints
import OAI.RepresentationTheory.Theta.Geometric.PresentedLevelComparison

/-! # Fiber Level -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.FiberLevel

noncomputable section

/-! The actual nearby reference isomorphism preserves the full ordered
level on every original test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance : IsReduced (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsReduced (Spec (.of ℂ)))

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
      (Universal.PELConditions.complexUniversalAction D.pel hg f) F)
    (z₀ : H.compatible.neighborhood) (hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point)

variable {b : D.domain} (R' : D.ReferencePELPointData hg b)
    (z : H.compatible.neighborhood)

variable (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso_level (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (c : LocallyConstant T.left (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.Coefficients (3 * s) D.pel.level)) :
    ((((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).level.pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).hom.app (.op T)) c).val ≫
      (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom =
      ((((Universal.PELConditions.complexUniversalPolarized D.pel hg f).level.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).hom.app (.op T)) c).val := by
  apply PresentedLevelComparison.original_level_comparison_of_presented_points
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point) (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))))
    (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z))
    ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).level.pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).level.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom ?_ T c
  exact R.referenceFiberPolarizedIso_presented_level f H z₀ hz₀ R' z hs hdegree hk

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.FiberLevel
