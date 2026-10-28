import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestFieldMarking
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison

/-! # Test Marking Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The constructed field marking of an actual reference test fiber
has precisely the original distinguished reference Hodge line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referenceTestFiberIso Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.nativeReferenceTestFieldMarking_complex (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let A := M.complexTestFamily κ f
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action y
    ((M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy).restrictScalars ℚ).toLinearMap.baseChange ℂ u =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom).baseChange ℂ
        ((Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP).nativeComplexReferenceMarking u) := by
  let A := M.complexTestFamily κ f
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A.polarized A.action y
  let R := Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP
  have he : ((M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy).restrictScalars ℚ).toLinearMap =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom).comp
        R.nativeReferenceMarking.toLinearMap := by
    apply LinearMap.ext
    intro v
    exact M.nativeReferenceTestFieldMarking_apply hM κ hP hκ f a y hy v
  dsimp only
  rw [he, LinearMap.baseChange_comp]
  rfl

theorem Models.FinePELModel.nativeReferenceTestFieldMarking_kernel :
    (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action
      y s (M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy) P hP).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
  let A := M.complexTestFamily κ f
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action y
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A.polarized A.action y
  apply Submodule.ext
  intro v
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized y).variety
    (((M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy).restrictScalars ℚ).toLinearMap.baseChange ℂ
      (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v)) = 0 ↔ _
  rw [M.nativeReferenceTestFieldMarking_complex]
  exact (RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy) _).trans
    (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.nativeReferenceFirst_kernel P hP (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP) v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
