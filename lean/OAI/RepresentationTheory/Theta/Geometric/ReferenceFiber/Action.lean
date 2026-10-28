import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.PolarizedIso
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonAction

/-! # Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Action

noncomputable section

/-! The algebraized nearby reference isomorphism intertwines every
original integral PEL action as an actual scheme equation. -/

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

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso_action (c : NumberField.RingOfIntegers E) :
    ((Universal.PELConditions.complexUniversalAction D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).map c ≫
      (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom =
      (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom ≫
        ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).map c := by
  apply (R.referenceFiberNativeComparison f H z₀ hz₀ R' z hs hdegree hk).algebraicIso_action
    ((Universal.PELConditions.complexUniversalAction D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
  intro d v
  exact R.referenceFiberComparison_integer f H z₀ hz₀ R' z d v

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Action
