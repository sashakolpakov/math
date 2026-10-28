import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedMarking
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank

/-! # Transported Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The fixed rational reference label computes exactly the Hodge kernel
of the transported full-field marking on every compatible native fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.transportedNativeReferenceLabel_complex (z : H.compatible.neighborhood)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    let A := M.complexTestFamily κ f
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀).baseChange ℂ u) =
      ((M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z).restrictScalars ℚ).toLinearMap.baseChange ℂ u := by
  let A := M.complexTestFamily κ f
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  let := RepresentationTheory.Theta.Geometric.Family.PELCoordinates.familyPeriodScalarTower A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  have he : (H.rationalTransport z).toLinearMap.comp
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) =
      ((M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z).restrictScalars ℚ).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact M.transportedNativeReferenceLabel_value hM κ hP hκ f a H z₀ hz₀ z v
  dsimp only
  rw [← he, LinearMap.baseChange_comp]
  rfl

theorem Models.FinePELModel.transportedNativeReferenceMatrix_kernel (z : H.compatible.neighborhood) :
    (H.referenceMarkedMatrix P hP (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
      (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s
        (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z) P hP).ker := by
  apply Submodule.ext
  intro v
  change H.referenceMarkedMatrix P hP
    (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z v = 0 ↔ _
  rw [H.referenceMarkedMatrix_kernel_iff, M.transportedNativeReferenceLabel_complex]
  rfl

theorem Models.FinePELModel.transportedNativeReferenceMatrix_center :
    (H.referenceMarkedMatrix P hP (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z₀).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val} := by
  let e := M.nativeReferenceTestFiberIso hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  have : IsMonHom e.hom :=
    M.nativeReferenceTestFiberIso_group hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  exact H.referenceIsoLabel_kernel (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP) z₀ e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
