import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality

/-! # Isogeny Hodge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyHodge.AbelianIntrinsicAdapter

noncomputable section

/-! The inverse rational period map of an actual isogeny preserves
the actual Hodge kernel, because its native tangent map is injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps

variable {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem nativeIsogenyRationalEquiv_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv A B PA PB f).toLinearMap :=
  PeriodProjectionNaturality.IntrinsicLinearMaps.rationalLift_isHodgeMap (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap A B PA PB f)

theorem nativeIsogenyRationalEquiv_symm_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv A B PA PB f).symm.toLinearMap := by
  let e := IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv A B PA PB f
  let F := IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap A B PA PB f
  intro v hv
  let u := e.symm.toLinearMap.baseChange ℂ v
  have he : (IntegralMaps.IntrinsicLinearMaps.rationalLift F).baseChange ℂ u = v :=
    (LinearEquiv.baseChange ℚ ℂ _ _ e).apply_symm_apply v
  have hn : Maps.IntrinsicLinearMaps.linearLift F (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) u) = 0 :=
    (PeriodProjectionNaturality.IntrinsicLinearMaps.complexPeriodProjection_natural F u).symm.trans
      ((congrArg (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) he).trans hv)
  exact Finite.ComplexFibers.NativeLinearMaps.linearLift_injective_of_isFinite F (hn.trans (Maps.IntrinsicLinearMaps.linearLift F).map_zero.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyHodge.AbelianIntrinsicAdapter
