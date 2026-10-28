import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapDeterminants
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Localization Chart Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationChartParameters

noncomputable section

/-! Localizing the chart coordinate algebra imposes exactly the overlap determinant condition. -/

universe u v w

/-- Algebra maps from a principal localization are the maps making its denominator a unit. -/
def localizationAwayAlgHomEquiv {R : Type u} {P : Type v} {A : Type w}
    [CommRing R] [CommRing P] [CommRing A] [Algebra R P] [Algebra R A] (d : P) :
    (Localization.Away d →ₐ[R] A) ≃ {φ : P →ₐ[R] A // IsUnit (φ d)} where
  toFun f := ⟨f.comp (Algebra.algHom R P (Localization.Away d)),
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).map f⟩
  invFun φ := IsLocalization.Away.liftAlgHom d φ.property
  left_inv f := by
    apply IsLocalization.algHom_ext (Submonoid.powers d)
    ext p
    exact IsLocalization.Away.lift_eq d
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d).map f) p
  right_inv φ := by
    apply Subtype.ext
    ext p
    exact IsLocalization.Away.lift_eq d φ.property p

variable (R : Type u) [CommRing R] {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))

/-- Points lying in both the standard chart and the chart selected by the coordinate permutation. -/
def GrassmannOverlapPoint (A : Type v) [CommRing A] :=
  {c : Grassmann.Charts.GrassmannChart A (Fin l → A) k //
    Function.Bijective ((Grassmann.Charts.grassmannQuotientChartEquiv c).firstBlock
      (Chart.CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap)}

/-- The polynomial-coordinate bijection restricts precisely to the determinant-unit condition. -/
def grassmannOverlapPolynomialEquiv (A : Type v) [CommRing A] [Algebra R A] :
    {φ : MvPolynomial (Fin k × Fin l) R →ₐ[R] A // IsUnit (φ (Chart.OverlapDeterminants.chartOverlapPolynomial R τ))} ≃
      GrassmannOverlapPoint τ A where
  toFun φ := ⟨Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv φ.val,
    (Chart.OverlapDeterminants.chartOverlapPolynomial_isUnit_iff φ.val τ).mp φ.property⟩
  invFun c := ⟨Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv.symm c.val,
    (Chart.OverlapDeterminants.chartOverlapPolynomial_isUnit_iff (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv.symm c.val) τ).mpr
      (by simpa only [Equiv.apply_symm_apply] using c.property)⟩
  left_inv φ := Subtype.ext (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv.symm_apply_apply φ.val)
  right_inv c := Subtype.ext (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv.apply_symm_apply c.val)

/-- The localized coordinate algebra parametrizes exactly the overlap points. -/
def grassmannOverlapAlgHomEquiv (A : Type v) [CommRing A] [Algebra R A] :
    (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ) →ₐ[R] A) ≃ GrassmannOverlapPoint τ A :=
  (localizationAwayAlgHomEquiv (Chart.OverlapDeterminants.chartOverlapPolynomial R τ)).trans
    (grassmannOverlapPolynomialEquiv R τ A)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationChartParameters
