import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosati

/-! # Quotient Rosati Condition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosatiCondition.Construction

noncomputable section

/-! The complete target Rosati condition, including its actual
Poincare equation, is derived from the source and the quotient
polarization identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E k : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (Q : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny P.abelian Q.abelian)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) Q.abelian)
variable (hσ : ∀ a : NumberField.RingOfIntegers E, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)

include hσ in
theorem quotient_rosati (m : ℕ)
    (hpol : PolarizationComparison.Construction.polarizationPullbackHom f.hom P.dual Q.dual Q.polarization = P.polarization.isogeny.hom ^ m)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ) : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation Q σ := by
  intro a
  refine ⟨PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) Q.dual Q.dual, inferInstance,
    IntrinsicPoincare.Construction.IntrinsicPicardPullback.dualMap_poincare Q.dual Q.dual (σ.map a), ?_⟩
  exact QuotientRosati.Construction.quotient_rosati_canonicalDual f P.dual Q.dual P.polarization Q.polarization ρ σ hσ m hpol
    a (NumberField.IsCMField.ringOfIntegersComplexConj E a) (PicardAdjoints.Construction.rosati_canonicalDual P ρ hρ a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosatiCondition.Construction
