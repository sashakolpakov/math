import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Away Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

noncomputable section

/-! A ring evaluation with invertible homogeneous denominator extends
to the degree-zero chart ring, with an exact cross-multiplication formula. -/
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A]
variable (g : ℕ → Submodule R S) [GradedAlgebra g] (f : S)
variable (φ : S →+* A) (hf : IsUnit (φ f))

def homogeneousAwayEvaluation : HomogeneousLocalization.Away g f →+* A :=
  (IsLocalization.Away.lift f hf : Localization.Away f →+* A).comp
    (algebraMap (HomogeneousLocalization.Away g f) (Localization.Away f))

theorem homogeneousAwayEvaluation_mk_cross {d : ℕ} (hfd : f ∈ g d)
    (k : ℕ) (p : S) (hp : p ∈ g (k • d)) :
    homogeneousAwayEvaluation g f φ hf (HomogeneousLocalization.Away.mk g hfd k p hp) *
        φ f ^ k = φ p := by
  have h := congrArg (IsLocalization.Away.lift f hf : Localization.Away f →+* A)
    (IsLocalization.mk'_spec (Localization.Away f) p (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f))
  simpa only [homogeneousAwayEvaluation, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', map_mul, IsLocalization.Away.lift_eq, map_pow] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation
