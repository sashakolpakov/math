import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction

/-! # Polarized Comparison Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! An algebraized native polarized comparison retains every original
integral action when its actual rational period map intertwines them. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E]
    {g N : ℕ} {δ : Fin g → ℕ}
    {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (D : PolarizedComparison.NativePolarizedComparison A B)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (hact : ∀ (a : NumberField.RingOfIntegers E)
      (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))),
      D.periods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ a v) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ a (D.periods v))

include hact in
theorem PolarizedComparison.NativePolarizedComparison.algebraicIso_action (a : NumberField.RingOfIntegers E) :
    ρ.map a ≫ D.algebraicIso.hom = D.algebraicIso.hom ≫ σ.map a := by
  unfold PolarizedComparison.NativePolarizedComparison.algebraicIso AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_intertwines A.abelian B.abelian
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B)
    D.periods D.hodge (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ D.periods D.hodge) D.integral ρ σ ?_ a
  intro b
  apply LinearMap.ext
  intro v
  exact hact b v

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
