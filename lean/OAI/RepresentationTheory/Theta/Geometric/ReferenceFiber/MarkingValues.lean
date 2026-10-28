import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.HodgeComparison
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedLattice

/-! # Marking Values -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.MarkingValues

noncomputable section

section

/-! The nearby reference-fiber comparison retains the exact original
full lattice, trace polarization, and every integral PEL endomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance : IsReduced (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsReduced (Spec (.of ℂ)))

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso
attribute [local irreducible] PolarizedCanonicalForm.familyPolarizationForm AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm

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

variable {b : D.domain} (R' : D.ReferencePELPointData hg b)
    (z : H.compatible.neighborhood)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison_integral
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety ↔
        R.referenceFiberComparison f H z₀ hz₀ R' z v ∈
          AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
            (Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  apply FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integral
  intro w
  exact (R'.nativeUniversalRationalMarking_integral R'.point
    (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) w).trans
    (R.transportedFieldMarking_integral f H z₀ hz₀ z w).symm

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison_polarization
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    PolarizedCanonicalForm.familyPolarizationForm (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
      (R.referenceFiberComparison f H z₀ hz₀ R' z v) (R.referenceFiberComparison f H z₀ hz₀ R' z w) =
        PolarizedCanonicalForm.familyPolarizationForm (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
          (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) v w := by
  apply FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_polarization
  intro u t
  exact (R.transportedFieldMarking_polarization f H z₀ hz₀ z u t).trans
    (R'.nativeUniversalRationalMarking_polarization R'.point
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) u t).symm

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison_integer (c : NumberField.RingOfIntegers E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    R.referenceFiberComparison f H z₀ hz₀ R' z
      (Family.FieldActions.familyIntegralPeriodAction (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
        (Universal.PELConditions.complexUniversalAction D.pel hg R'.point) (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) c v) =
      Family.FieldActions.familyIntegralPeriodAction (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
        (Intrinsic.FamilyFrames.familyChartParameter C z) c (R.referenceFiberComparison f H z₀ hz₀ R' z v) :=
  FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integer _ _ _ _ _ _ _ _ c v

end ActiveHeckeThetaData.ReferencePELPointData

end

/-! The reference-to-nearby comparison sends each original rational
reference vector to its exact transported field marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance : IsReduced (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsReduced (Spec (.of ℂ)))

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso
attribute [local irreducible] PolarizedCanonicalForm.familyPolarizationForm AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm

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

variable {b : D.domain} (R' : D.ReferencePELPointData hg b)
    (z : H.compatible.neighborhood)

attribute [local irreducible] FieldMarkingCoordinateChange.fieldMarkingPeriodComparison Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    R.referenceFiberComparison f H z₀ hz₀ R' z
      (R'.nativeUniversalRationalMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v) =
        R.transportedFieldMarking f H z₀ hz₀ z v := by
  have he := FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking
    (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point) (Universal.PELConditions.complexUniversalAction D.pel hg R'.point)
    (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
    (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
    (R'.nativeUniversalFieldMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (R.transportedFieldMarking f H z₀ hz₀ z) v
  rw [R'.nativeUniversalFieldMarking_apply] at he
  exact he

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.MarkingValues
