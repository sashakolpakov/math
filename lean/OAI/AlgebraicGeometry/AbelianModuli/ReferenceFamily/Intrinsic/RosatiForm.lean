import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodAdjoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.RosatiExtension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps

/-! # Rosati Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RosatiForm

noncomputable section

/-! The actual native polarization form is balanced for the full CM
field action. The integral Rosati formula comes from the original
Poincare bundle; the rational tensor presentation extends it to E. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FieldMaps.IntrinsicNumberFieldAction

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}

theorem nativePolarizationForm_rosati
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) :
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
    let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
    Hermitian.Reconstruction.TraceReconstruction.RosatiBalanced (E := E) (ChernPairing.nativePolarizationForm A) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  apply Integral.RosatiExtension.rosatiBalanced_of_integers
  intro a x y
  have h := ActionData.RosatiConjugation.period_adjoint A ρ hρ
    (NumberField.IsCMField.ringOfIntegersComplexConj E a) x y
  rw [Polarization.PeriodAdjoints.integralConjugation_involutive] at h
  change ChernPairing.nativePolarizationForm A (NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ a x) y =
    ChernPairing.nativePolarizationForm A x (NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) y) at h
  have hl := NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ a x
  have hr := NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
    (NumberField.IsCMField.ringOfIntegersComplexConj E a) y
  exact (congrArg (fun v => ChernPairing.nativePolarizationForm A v y) hl).trans
    (h.trans (congrArg (ChernPairing.nativePolarizationForm A x) hr.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RosatiForm
