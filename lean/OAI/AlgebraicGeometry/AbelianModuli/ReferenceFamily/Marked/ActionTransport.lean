import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Action Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ActionTransport.IntrinsicPELMarking

noncomputable section

/-! E-linearity of a change of marking gives the actual integral PEL
action equations on rational periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

theorem markedPeriodTransport_field_action (a : E) (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A PA ρ a v) =
      Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction B PB σ a (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u v) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B PB σ
  exact ((Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree).trans
    (u.trans (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree).symm)).map_smul a v

theorem markedPeriodTransport_integral_action (a : NumberField.RingOfIntegers E) :
    (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap.comp
        (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a)).comp
        (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap := by
  apply LinearMap.ext
  intro v
  let t := PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u
  change t (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A PA ρ a v) = Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction B PB σ a (t v)
  exact (congrArg t (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A PA ρ a v)).symm.trans
    ((markedPeriodTransport_field_action A B PA PB ρ σ s hs hg hdegree u (a : E) v).trans
      (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply B PB σ a (t v)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ActionTransport.IntrinsicPELMarking
