import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedFieldMarking
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.Polarization
import OAI.RepresentationTheory.Theta.Geometric.Relative.IntegralPolarization

/-! # Transported Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The transported full field marking preserves the original reference
trace form at every fiber in its common compatible neighborhood. -/

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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking_polarization (z : H.compatible.neighborhood) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    PolarizedCanonicalForm.familyPolarizationForm (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
      (R.transportedFieldMarking f H z₀ hz₀ z v) (R.transportedFieldMarking f H z₀ hz₀ z w) =
        D.pel.reference.traceForm v w := by
  rw [R.transportedFieldMarking_apply, R.transportedFieldMarking_apply]
  exact (H.compatible.rationalBetween_polarization (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
    (Universal.PELConditions.complexUniversalAction D.pel hg f) z₀ z
    (R.nativeUniversalRationalMarking f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)
    (R.nativeUniversalRationalMarking f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ w)).trans
      (R.nativeUniversalRationalMarking_polarization f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v w)

end

end OAI.RepresentationTheory.Theta.Geometric
