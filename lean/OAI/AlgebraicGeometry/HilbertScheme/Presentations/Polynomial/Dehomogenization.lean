import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Dehomogenization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient

/-! # Dehomogenization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective

noncomputable section

/-!
Dehomogenization on projective polynomial charts with an arbitrary variable
index type. Homogeneous polynomials map to fractions with the corresponding
power of the selected coordinate as denominator.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}

abbrev polynomialGrading (σ : Type v) (R : Type u) [CommRing R] :=
  homogeneousSubmodule σ R

instance polynomialGradedAlgebra : GradedAlgebra (polynomialGrading σ R) :=
  MvPolynomial.gradedAlgebra

def coordinateFraction (i : σ) (d : ℕ) (f : polynomialGrading σ R d) :
    HomogeneousLocalization.Away (polynomialGrading σ R) (X i) :=
  HomogeneousLocalization.Away.mk (polynomialGrading σ R) (isHomogeneous_X R i) d f.val
    (by simpa only [smul_eq_mul, mul_one] using f.property)

def coordinateConstants : R →+* polynomialGrading σ R 0 where
  toFun r := ⟨C r, isHomogeneous_C _ r⟩
  map_one' := Subtype.ext (map_one C)
  map_zero' := Subtype.ext (map_zero C)
  map_add' r s := Subtype.ext (map_add C r s)
  map_mul' r s := Subtype.ext (map_mul C r s)

def chartConstants (i : σ) :
    R →+* HomogeneousLocalization.Away (polynomialGrading σ R) (X i) :=
  (fromZeroRingHom (polynomialGrading σ R) (Submonoid.powers (X i))).comp coordinateConstants

def dehomogenize (i : σ) :
    MvPolynomial σ R →+* HomogeneousLocalization.Away (polynomialGrading σ R) (X i) :=
  eval₂Hom (chartConstants i) (fun j => coordinateFraction i 1 ⟨X j, isHomogeneous_X R j⟩)

theorem dehomogenize_X (i j : σ) :
    dehomogenize (R := R) i (X j) =
      coordinateFraction i 1 ⟨X j, isHomogeneous_X R j⟩ := eval₂_X _ _ _

theorem dehomogenize_C (i : σ) (r : R) :
    dehomogenize i (C r) = chartConstants i r := eval₂Hom_C _ _ _

theorem val_chartConstants (i : σ) (r : R) :
    (chartConstants i r).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (C r) := by
  change Localization.mk (C r) 1 = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]

theorem val_coordinateFraction (i : σ) (d : ℕ) (f : polynomialGrading σ R d) :
    (coordinateFraction i d f).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) f.val *
        IsLocalization.Away.invSelf (X (R := R) i) ^ d := by
  erw [coordinateFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  rw [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf (X (R := R) i)),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem dehomogenize_homogeneous (i : σ) {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    dehomogenize i f = coordinateFraction i d ⟨f, hf⟩ := by
  apply HomogeneousLocalization.val_injective
  let φ := algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))
  let c : Localization.Away (X (R := R) i) := IsLocalization.Away.invSelf (X (R := R) i)
  have hmap : (algebraMap (HomogeneousLocalization.Away (polynomialGrading σ R) (X i))
      (Localization.Away (X (R := R) i))).comp (dehomogenize i) =
      eval₂Hom (φ.comp C) (fun j => c * φ (X j)) := by
    ext r
    · simp only [RingHom.comp_apply, eval₂Hom_C, dehomogenize_C,
        HomogeneousLocalization.algebraMap_apply, val_chartConstants]
      rfl
    · simp only [RingHom.comp_apply, eval₂Hom_X', dehomogenize_X,
        HomogeneousLocalization.algebraMap_apply, val_coordinateFraction, pow_one]
      exact mul_comm _ _
  have hplain : eval₂Hom (φ.comp C) (fun j => φ (X j)) = φ := by
    ext <;> simp
  change ((algebraMap _ _).comp (dehomogenize i)) f = _
  rw [hmap, Dehomogenization.GradedHilbert.homogeneous_eval₂_scale _ _ _ hf, hplain, val_coordinateFraction, mul_comm]

theorem dehomogenize_self (i : σ) : dehomogenize (R := R) i (X i) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [dehomogenize_X, val_coordinateFraction, pow_one, HomogeneousLocalization.val_one,
    IsLocalization.Away.mul_invSelf]

theorem dehomogenize_surjective (i : σ) :
    Function.Surjective (dehomogenize (R := R) i) := by
  intro z
  obtain ⟨d, f, hf, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (polynomialGrading σ R) (isHomogeneous_X R i) z
  have hf' : f ∈ polynomialGrading σ R d := by simpa only [smul_eq_mul, mul_one] using hf
  exact ⟨f, dehomogenize_homogeneous i hf'⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective
