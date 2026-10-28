import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedFieldMarking
import OAI.RepresentationTheory.Theta.Geometric.Reference.IsoLabels

/-! # Transported Label -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The transported reference field marking is represented by one
fixed rational label in the original holomorphic central period frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
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

def Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceLabel : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E)
    (A := Universal.PELConditions.complexUniversalPolarized D.pel hg f) (C := C) := by
  let e := R.nativeUniversalFiberIso f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  let : IsMonHom e.hom := R.nativeUniversalFiberIso_group f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  exact H.referenceIsoLabel (R.model.toNativeReferenceModel R.analytic) z₀ e

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceLabel_value (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    H.rationalTransport z (R.transportedReferenceLabel f H z₀ hz₀ v) =
      R.transportedFieldMarking f H z₀ hz₀ z v := by
  rw [R.transportedFieldMarking_apply]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
