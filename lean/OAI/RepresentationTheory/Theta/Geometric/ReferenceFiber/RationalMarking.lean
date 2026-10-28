import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.IntrinsicRational
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.MarkingValues

/-! # Rational Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.RationalMarking

noncomputable section

/-! The algebraized native comparison sends each original rational
reference vector to its exact nearby transported marking. -/

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

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift
      ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso
        ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).abelian.pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation
          ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).hom ≫
        (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom ≫
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso
          ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
          (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation
            ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left))).inv)
        (R'.nativeUniversalRationalMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v) =
          R.transportedFieldMarking f H z₀ hz₀ z v := by
  have hr := R.referenceFiberPolarizedIso_rational f H z₀ hz₀ R' z hs hdegree hk
  have hv := LinearMap.congr_fun hr
    (R'.nativeUniversalRationalMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v)
  exact hv.trans (R.referenceFiberComparison_marking f H z₀ hz₀ R' z v)

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.RationalMarking
