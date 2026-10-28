import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealRecovery

/-! # Dehomogenization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Dehomogenization.GradedHilbert

noncomputable section

/-!
Dehomogenization on the standard affine charts of projective space.
These are ring homomorphisms, and a homogeneous polynomial of degree d
maps to its fraction with denominator the d-th power of the chart coordinate.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u

theorem homogeneous_eval₂_scale {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (v : σ → S) (c : S) {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    eval₂Hom φ (fun j => c * v j) f = c ^ d * eval₂Hom φ v f := by
  classical
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial a r ha =>
    have had : a.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using ha
    simp only [eval₂Hom_monomial, mul_pow, Finsupp.prod_mul]
    have hpow : a.prod (fun _ k => c ^ k) = c ^ a.degree := by
      change (∏ j ∈ a.support, c ^ a j) = c ^ ∑ j ∈ a.support, a j
      rw [Finset.prod_pow_eq_pow_sum]
    rw [hpow, had]
    ring

variable {R : Type u} [CommRing R] {n : ℕ}

def coordinateConstants : R →+* Hilbert.Polynomial.GradedHilbert.grading R n 0 where
  toFun r := ⟨C r, isHomogeneous_C _ r⟩
  map_one' := Subtype.ext (map_one C)
  map_zero' := Subtype.ext (map_zero C)
  map_add' r s := Subtype.ext (map_add C r s)
  map_mul' r s := Subtype.ext (map_mul C r s)

def chartConstants (i : Fin (n + 1)) :
    R →+* HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) :=
  (fromZeroRingHom (Hilbert.Polynomial.GradedHilbert.grading R n) (Submonoid.powers (X i))).comp coordinateConstants

def dehomogenize (i : Fin (n + 1)) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →+* HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) :=
  eval₂Hom (chartConstants i) (fun j => Projective.IdealRecovery.GradedHilbert.coordinateFraction i 1 ⟨X j, isHomogeneous_X R j⟩)

theorem dehomogenize_X (i j : Fin (n + 1)) :
    dehomogenize (R := R) i (X j) =
      Projective.IdealRecovery.GradedHilbert.coordinateFraction i 1 ⟨X j, isHomogeneous_X R j⟩ := eval₂_X _ _ _

theorem dehomogenize_C (i : Fin (n + 1)) (r : R) :
    dehomogenize i (C r) = chartConstants i r := eval₂Hom_C _ _ _

theorem val_chartConstants (i : Fin (n + 1)) (r : R) :
    (chartConstants i r).val =
      algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i)) (C r) := by
  change Localization.mk (C r) 1 = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]

theorem val_coordinateFraction (i : Fin (n + 1)) (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (Projective.IdealRecovery.GradedHilbert.coordinateFraction i d f).val =
      algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i)) f.val *
        IsLocalization.Away.invSelf (X (R := R) i) ^ d := by
  erw [Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  rw [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf (X (R := R) i)),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem dehomogenize_homogeneous (i : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    dehomogenize i f = Projective.IdealRecovery.GradedHilbert.coordinateFraction i d ⟨f, hf⟩ := by
  apply HomogeneousLocalization.val_injective
  let φ := algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i))
  let c : Localization.Away (X (R := R) i) := IsLocalization.Away.invSelf (X (R := R) i)
  have hmap : (algebraMap (HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
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
  rw [hmap, homogeneous_eval₂_scale _ _ _ hf, hplain, val_coordinateFraction, mul_comm]

theorem dehomogenize_self (i : Fin (n + 1)) : dehomogenize (R := R) i (X i) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [dehomogenize_X, val_coordinateFraction, pow_one, HomogeneousLocalization.val_one,
    IsLocalization.Away.mul_invSelf]

theorem dehomogenize_surjective (i : Fin (n + 1)) :
    Function.Surjective (dehomogenize (R := R) i) := by
  intro z
  obtain ⟨d, f, hf, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) z
  have hf' : f ∈ Hilbert.Polynomial.GradedHilbert.grading R n d := by simpa only [smul_eq_mul, mul_one] using hf
  exact ⟨f, dehomogenize_homogeneous i hf'⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Dehomogenization.GradedHilbert
