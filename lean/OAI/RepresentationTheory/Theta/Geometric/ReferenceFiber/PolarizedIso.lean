import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.MarkingValues
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison

/-! # Polarized Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.PolarizedIso

noncomputable section

/-! Algebraize the actual nearby reference comparison into an original
polarized abelian-scheme isomorphism with its exact polarization map. -/

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

attribute [local irreducible] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberNativeComparison : Intrinsic.PolarizedComparison.NativePolarizedComparison
    ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) where
  periods := R.referenceFiberComparison f H z₀ hz₀ R' z
  hodge := R.referenceFiberComparison_isHodgeMap f H z₀ hz₀ R' z hs hdegree hk
  integral := fun v => R.referenceFiberComparison_integral f H z₀ hz₀ R' z v
  polarization := fun v w => R.referenceFiberComparison_polarization f H z₀ hz₀ R' z v w

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberNativeComparison

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso :
    ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).abelian.pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).scheme ≅
      ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).scheme :=
  (R.referenceFiberNativeComparison f H z₀ hz₀ R' z hs hdegree hk).algebraicIso

instance _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso_group :
    IsMonHom (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom :=
  (R.referenceFiberNativeComparison f H z₀ hz₀ R' z hs hdegree hk).algebraicIso_group

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.PolarizedIso
