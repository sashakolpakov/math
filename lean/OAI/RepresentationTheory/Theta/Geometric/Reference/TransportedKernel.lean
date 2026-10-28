import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedLabel
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
import OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank

/-! # Transported Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual transported reference label has a one-dimensional
active kernel throughout the original compatible neighborhood. -/

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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceLabel_complex (z : H.compatible.neighborhood)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
      (Universal.PELConditions.complexUniversalAction D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((R.transportedReferenceLabel f H z₀ hz₀).baseChange ℂ u) =
      ((R.transportedFieldMarking f H z₀ hz₀ z).restrictScalars ℚ).toLinearMap.baseChange ℂ u := by
  let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
  let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  have heq : (H.rationalTransport z).toLinearMap.comp (R.transportedReferenceLabel f H z₀ hz₀) =
      ((R.transportedFieldMarking f H z₀ hz₀ z).restrictScalars ℚ).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact R.transportedReferenceLabel_value f H z₀ hz₀ z v
  dsimp only
  rw [← heq, LinearMap.baseChange_comp]
  rfl

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceMatrix_kernel (z : H.compatible.neighborhood) :
    (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker =
      (FieldMarkingKernelRank.fieldMarkingFirstProjection (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
        (Universal.PELConditions.complexUniversalAction D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z) s
        (R.transportedFieldMarking f H z₀ hz₀ z) D.pel.reference hg.reference_admissible).ker := by
  apply Submodule.ext
  intro v
  change H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
    (R.transportedReferenceLabel f H z₀ hz₀) z v = 0 ↔ _
  rw [H.referenceMarkedMatrix_kernel_iff, R.transportedReferenceLabel_complex]
  rfl

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceMatrix_finrank (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : H.compatible.neighborhood) :
    Module.finrank ℂ (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker = 1 := by
  rw [R.transportedReferenceMatrix_kernel]
  exact FieldMarkingKernelRank.fieldMarkingFirstProjection_finrank (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
    (Universal.PELConditions.complexUniversalAction D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z) s hs rfl hdegree
    (R.transportedFieldMarking f H z₀ hz₀ z) D.pel.reference hg.reference_admissible
    (Universal.DistinguishedRank.complexUniversal_distinguished_rank D.pel hg f (Intrinsic.FamilyFrames.familyChartParameter C z))

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceMatrix_center :
    (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z₀).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
  let e := R.nativeUniversalFiberIso f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  let : IsMonHom e.hom := R.nativeUniversalFiberIso_group f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  exact H.referenceIsoLabel_kernel (R.model.toNativeReferenceModel R.analytic) z₀ e

end

end OAI.RepresentationTheory.Theta.Geometric
