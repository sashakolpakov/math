import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.FieldMarking
import OAI.RepresentationTheory.Theta.Geometric.Relative.FieldEquiv
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.HolomorphicTransport

/-! # Transported Field Marking -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Transport the actual reference marking over the complete field
action to every fiber in the same compatible neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

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

def Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking (z : H.compatible.neighborhood) :
    let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
    let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
  let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z₀)
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  exact (R.nativeUniversalFieldMarking f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀).trans
    (H.compatible.fieldBetween A ρ z₀ z)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking_apply (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.transportedFieldMarking f H z₀ hz₀ z v =
      H.compatible.rationalBetween (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
        z₀ z (R.nativeUniversalRationalMarking f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v) := by
  unfold Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking
  rw [LinearEquiv.trans_apply, Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldBetween_apply,
    R.nativeUniversalFieldMarking_apply]

end

end OAI.RepresentationTheory.Theta.Geometric
