import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedFieldMarking
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.Lattice
import OAI.RepresentationTheory.Theta.Geometric.Relative.IntegralPolarization

/-! # Transported Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The full original reference lattice remains unchanged under the
actual field marking throughout the compatible neighborhood. -/

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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking_integral (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.transportedFieldMarking f H z₀ hz₀ z v ∈
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods
        (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)).variety ↔
          v ∈ D.pel.reference.lattice := by
  rw [R.transportedFieldMarking_apply]
  exact (H.compatible.rationalBetween_integral (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
    (Universal.PELConditions.complexUniversalAction D.pel hg f) z₀ z
    (R.nativeUniversalRationalMarking f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)).trans
      (R.nativeUniversalRationalMarking_integral f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)

end

end OAI.RepresentationTheory.Theta.Geometric
