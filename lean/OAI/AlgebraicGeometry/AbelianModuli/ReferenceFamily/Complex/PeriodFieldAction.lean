import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.RosatiExtension

/-! # Period Field Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodFieldAction.IntrinsicNumberFieldAction

noncomputable section

/-! The full number field acts on the genuine native complex tangent
space, and the actual complexified period projection is equivariant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def complexFieldAction : E →ₐ[ℚ] Module.End ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :=
  Integral.ActionExtension.extendIntegralAction (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ)

theorem complexFieldAction_integer (a : NumberField.RingOfIntegers E) :
    complexFieldAction A P ρ (a : E) = Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ a :=
  Integral.ActionExtension.extendIntegralAction_integer (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A P ρ) a

theorem complexPeriodProjection_fieldAction (a : E)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ((Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ u) =
      complexFieldAction A P ρ a (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) u) := by
  let U := Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
  let V := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
  let π : ComplexMultiplication.WeightOne.CM.Complexification U →ₗ[ℂ] V := Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)
  let F : E →ₗ[ℚ] V := (π.restrictScalars ℚ).comp
    ((LinearMap.applyₗ' ℚ u).comp
      ((LinearMap.baseChangeHom ℚ ℂ U U).comp (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ).toLinearMap))
  let G : E →ₗ[ℚ] V := (LinearMap.applyₗ' ℚ (π u)).comp (complexFieldAction A P ρ).toLinearMap
  have hi (b : NumberField.RingOfIntegers E) : F (b : E) = G (b : E) := by
    change π ((Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ (b : E)).baseChange ℂ u) = complexFieldAction A P ρ (b : E) (π u)
    have hf : Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ (b : E) = Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A P ρ b :=
      LinearMap.ext (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A P ρ b)
    rw [hf, complexFieldAction_integer]
    exact PeriodProjectionNaturality.IntrinsicLinearMaps.complexPeriodProjection_natural (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A P ρ b) u
  have he : F = G := Integral.RosatiExtension.rationalLinearMap_eq_of_integers (E := E) (W := V) F G hi
  exact LinearMap.congr_fun he a

theorem fieldAction_isHodgeMap (a : E) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a) := by
  intro u hu
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ((Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A P ρ a).baseChange ℂ u) = 0
  exact (complexPeriodProjection_fieldAction A P ρ a u).trans
    ((congrArg (complexFieldAction A P ρ a) hu).trans (complexFieldAction A P ρ a).map_zero)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.PeriodFieldAction.IntrinsicNumberFieldAction
