import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction

/-! # Determinant Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantEvaluation

noncomputable section

/-! Changing the target of a determinant-valued functional commutes
with evaluation on the conormal generator. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantAdjunction

universe u v w t s

variable {A : Type u} [CommRing A]
  {U : Type v} [AddCommGroup U] [Module A U]
  {V : Type w} [AddCommGroup V] [Module A V]
  {W : Type t} [AddCommGroup W] [Module A W]
  {Z : Type s} [AddCommGroup Z] [Module A Z]
  {c : ℕ} (b : Module.Basis (Fin c) A U)

theorem ofResidue_arrow (e : V ≃ₗ[A] W) (r : W ≃ₗ[A] Z) (φ : (⋀[A]^c U) →ₗ[A] V) :
    DeterminantAdjunction.ofResidue b r (((LinearEquiv.refl A (⋀[A]^c U)).arrowCongr e) φ) =
      r (e (DeterminantAdjunction.evaluation b φ)) := by
  rw [DeterminantAdjunction.ofResidue_apply, LinearEquiv.arrowCongr_apply, DeterminantAdjunction.evaluation_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantEvaluation
