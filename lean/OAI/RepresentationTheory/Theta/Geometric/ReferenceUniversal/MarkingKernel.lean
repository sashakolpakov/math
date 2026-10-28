import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.FieldMarking
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison

/-! # Marking Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual reference marking of a universal fiber has exactly the
original reference line as its distinguished complex kernel. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFieldMarking_complex (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x
    ((R.nativeUniversalFieldMarking f x hx).restrictScalars ℚ).toLinearMap.baseChange ℂ u =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (R.nativeUniversalFiberIso f x hx).hom).baseChange ℂ
        ((R.model.toNativeReferenceModel R.analytic).nativeComplexReferenceMarking u) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x
  let := Family.PELCoordinates.familyPeriodScalarTower (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x
  let M := R.model.toNativeReferenceModel R.analytic
  have he : ((R.nativeUniversalFieldMarking f x hx).restrictScalars ℚ).toLinearMap =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (R.nativeUniversalFiberIso f x hx).hom).comp M.nativeReferenceMarking.toLinearMap := by
    apply LinearMap.ext
    intro v
    exact R.nativeUniversalFieldMarking_apply f x hx v
  dsimp only
  rw [he, LinearMap.baseChange_comp]
  rfl

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFieldMarking_kernel :
    (FieldMarkingKernelRank.fieldMarkingFirstProjection (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
      x s (R.nativeUniversalFieldMarking f x hx) D.pel.reference hg.reference_admissible).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x
  let := Family.PELCoordinates.familyPeriodScalarTower (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f) x
  apply Submodule.ext
  intro v
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).variety
    (((R.nativeUniversalFieldMarking f x hx).restrictScalars ℚ).toLinearMap.baseChange ℂ
      (Reference.FirstEmbedding.referenceFirstComplexInclusion D.pel.reference hg.reference_admissible v)) = 0 ↔ _
  rw [R.nativeUniversalFieldMarking_complex]
  exact (Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff (R.nativeUniversalFiberIso f x hx) _).trans
    (Reference.FirstEmbedding.nativeReferenceFirst_kernel D.pel.reference hg.reference_admissible
      (R.model.toNativeReferenceModel R.analytic) v)

end

end OAI.RepresentationTheory.Theta.Geometric
