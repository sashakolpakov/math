import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat

/-! # Chart Algebra Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEvaluation

noncomputable section

/-! Evaluation from a homogeneous chart preserves its coefficient algebra. -/
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert
universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type v} [CommRing A] [Algebra R A]

theorem homogeneousAwayEvaluation_coefficients (g : ℕ → Submodule R S) [GradedAlgebra g]
    (f : S) (φ : S →ₐ[R] A) (hf : IsUnit (φ f)) (r : R) :
    AwayEvaluation.homogeneousAwayEvaluation g f φ.toRingHom hf
        (algebraMap R (HomogeneousLocalization.Away g f) r) = algebraMap R A r := by
  unfold AwayEvaluation.homogeneousAwayEvaluation
  rw [RingHom.comp_apply, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  change (IsLocalization.Away.lift f hf : Localization.Away f →+* A)
    (Localization.mk (algebraMap R S r) 1) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one, IsLocalization.Away.lift_eq]
  exact φ.commutes r

def homogeneousAwayAlgebraEvaluation (g : ℕ → Submodule R S) [GradedAlgebra g]
    (f : S) (φ : S →ₐ[R] A) (hf : IsUnit (φ f)) :
    HomogeneousLocalization.Away g f →ₐ[R] A where
  __ := AwayEvaluation.homogeneousAwayEvaluation g f φ.toRingHom hf
  commutes' := homogeneousAwayEvaluation_coefficients g f φ hf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEvaluation
