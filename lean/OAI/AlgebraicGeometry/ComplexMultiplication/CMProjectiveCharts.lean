import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap
import OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs

/-! # CM Projective Charts -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMProjectiveCharts.ProjectiveCharts

noncomputable section

/-! # Standard Proj chart rings over an arbitrary coefficient ring

The two inverse maps use the actual degree-zero localization. This generalizes
the older complex-coefficient chart argument for comparing the two projective
presentations; it does not identify their schemes by definition.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable (R : Type) [CommRing R]

abbrev homogeneousCoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) R

abbrev projectiveGrading (n : ℕ) : ℕ → Submodule R (homogeneousCoordinateRing R n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

instance projectiveGradedAlgebra (n : ℕ) : GradedAlgebra (projectiveGrading R n) :=
  MvPolynomial.gradedAlgebra

def degreeZeroConstants (n : ℕ) : R ≃+* projectiveGrading R n 0 :=
  (Foundations.ProjectiveSpaceIs.ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) R).symm

@[simp]
theorem degreeZeroConstants_coe (n : ℕ) (r : R) :
    (degreeZeroConstants R n r : homogeneousCoordinateRing R n) = MvPolynomial.C r := rfl

/-- The homogeneous localization defining the standard `i`-th Proj chart. -/
abbrev projectiveChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (projectiveGrading R n) (MvPolynomial.X i)

/-- The affine polynomial coordinate ring, omitting the `i`-th variable. -/
abbrev projectiveChartPolynomial (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial {j : Fin (n + 1) // j ≠ i} R

theorem projectiveVariable_homogeneous (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ projectiveGrading R n 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- Constant coefficients in the actual homogeneous chart ring. -/
def projectiveChartConstants (n : ℕ) (i : Fin (n + 1)) :
    R →+* projectiveChartRing R n i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading R n)
    (Submonoid.powers (MvPolynomial.X i))).comp (degreeZeroConstants R n).toRingHom

/-- Setting `Xᵢ = 1` extends to the ordinary localization at `Xᵢ`. -/
def projectiveChartLocalizationToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n) →+*
      projectiveChartPolynomial R n i :=
  Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Dehomogenization restricted to the actual degree-zero localization. -/
def projectiveChartToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing R n i →+* projectiveChartPolynomial R n i :=
  (projectiveChartLocalizationToPolynomial R n i).comp
    (algebraMap (projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)))

/-- A homogeneous fraction `f / Xᵢ^k` maps exactly to `f(Xᵢ:= 1)`. -/
@[simp]
theorem projectiveChartToPolynomial_mk (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (f : homogeneousCoordinateRing R n)
    (hf : f ∈ projectiveGrading R n (k • (1 : ℕ))) :
    projectiveChartToPolynomial R n i
      (HomogeneousLocalization.Away.mk (projectiveGrading R n)
        (projectiveVariable_homogeneous R n i) k f hf) = Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f := by
  change Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk f ⟨MvPolynomial.X i ^ k, k, rfl⟩) = _
  simpa using Localization.awayLift_mk (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) f 1 (by simp) k

/-- Dehomogenization preserves the coefficient homomorphism to the chart. -/
@[simp]
theorem projectiveChartToPolynomial_constants (n : ℕ) (i : Fin (n + 1)) (c : R) :
    projectiveChartToPolynomial R n i (projectiveChartConstants R n i c) =
      MvPolynomial.C c := by
  change Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk (MvPolynomial.C c) ⟨1, Submonoid.one_mem _⟩) = _
  simpa using Localization.awayLift_mk (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) (MvPolynomial.C c) 1 (by simp) 0

/-- A degree-zero coordinate fraction in the actual standard Proj chart. -/
def projectiveChartRatio (n : ℕ) (i j : Fin (n + 1)) : projectiveChartRing R n i :=
  HomogeneousLocalization.Away.mk (projectiveGrading R n)
    (projectiveVariable_homogeneous R n i) 1 (MvPolynomial.X j)
    (by simpa using projectiveVariable_homogeneous R n j)

@[simp]
theorem projectiveChartToPolynomial_ratio (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    projectiveChartToPolynomial R n i (projectiveChartRatio R n i j.val) = X j := by
  simp [projectiveChartRatio, j.property]

/-- Map an affine polynomial into the homogeneous chart by coordinate ratios. -/
def polynomialToProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartPolynomial R n i →+* projectiveChartRing R n i :=
  MvPolynomial.eval₂Hom (projectiveChartConstants R n i)
    (fun j => projectiveChartRatio R n i j.val)

@[simp]
theorem polynomialToProjectiveChart_C (n : ℕ) (i : Fin (n + 1)) (c : R) :
    polynomialToProjectiveChart R n i (C c) = projectiveChartConstants R n i c := by
  simp [polynomialToProjectiveChart]

@[simp]
theorem polynomialToProjectiveChart_X (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    polynomialToProjectiveChart R n i (X j) = projectiveChartRatio R n i j.val := by
  simp [polynomialToProjectiveChart]

/-- Substitution back to affine polynomials is a left inverse. -/
theorem projectiveChartToPolynomial_comp (n : ℕ) (i : Fin (n + 1)) :
    (projectiveChartToPolynomial R n i).comp (polynomialToProjectiveChart R n i) =
      RingHom.id (projectiveChartPolynomial R n i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- The constants in the homogeneous chart have their expected value in the
ordinary localization. -/
@[simp]
theorem projectiveChartConstants_val (n : ℕ) (i : Fin (n + 1)) (c : R) :
    (projectiveChartConstants R n i c).val =
      algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Coordinate fractions have their expected value in the ordinary localization. -/
theorem projectiveChartRatio_val (n : ℕ) (i j : Fin (n + 1)) :
    (projectiveChartRatio R n i j).val =
      algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) (X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : homogeneousCoordinateRing R n) := by
  simp only [projectiveChartRatio, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- General homogeneous chart fractions have the expected inverse-power denominator. -/
theorem projectiveChartFraction_val (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : homogeneousCoordinateRing R n) (hf : f ∈ projectiveGrading R n (k • (1 : ℕ))) :
    (HomogeneousLocalization.Away.mk (projectiveGrading R n)
      (projectiveVariable_homogeneous R n i) k f hf).val =
      IsLocalization.Away.invSelf (S := Localization.Away
        (MvPolynomial.X i : homogeneousCoordinateRing R n))
        (MvPolynomial.X i : homogeneousCoordinateRing R n) ^ k *
      algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) f := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  simpa only [one_pow, SubmonoidClass.mk_pow, IsLocalization.Away.invSelf] using
    (IsLocalization.mk'_pow
      (S := Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n))
      (1 : homogeneousCoordinateRing R n)
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : homogeneousCoordinateRing R n)) k)

/-- Substitution by ratios in the ordinary localization is normalization of
all homogeneous variables by the same inverse of `X_i`. -/
theorem projectiveChart_normalization_map (n : ℕ) (i : Fin (n + 1)) :
    ((algebraMap (projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n))).comp
      (polynomialToProjectiveChart R n i)).comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) =
    MvPolynomial.eval₂Hom
      ((algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n))).comp C)
      (fun j => IsLocalization.Away.invSelf
        (MvPolynomial.X i : homogeneousCoordinateRing R n) *
        algebraMap (homogeneousCoordinateRing R n)
          (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [RingHom.comp_apply, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self, map_one, eval₂Hom_X']
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp [hj, projectiveChartRatio_val, mul_comm]

/-- Evaluation of all original variables through their localization images
is the localization homomorphism itself. -/
theorem projectiveChart_unnormalized_map (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.eval₂Hom
      ((algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n))).comp C)
      (fun j => algebraMap (homogeneousCoordinateRing R n)
        (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) (X j)) =
    algebraMap (homogeneousCoordinateRing R n)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- Every homogeneous chart fraction is the polynomial in coordinate ratios
obtained by dehomogenizing its numerator. -/
theorem polynomialToProjectiveChart_dehomogenize (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : homogeneousCoordinateRing R n) (hf : f ∈ projectiveGrading R n (k • (1 : ℕ))) :
    polynomialToProjectiveChart R n i (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f) =
      HomogeneousLocalization.Away.mk (projectiveGrading R n)
        (projectiveVariable_homogeneous R n i) k f hf := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  change (((algebraMap (projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : homogeneousCoordinateRing R n))).comp
      (polynomialToProjectiveChart R n i)).comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)) f = _
  rw [projectiveChart_normalization_map, projectiveChartFraction_val]
  have hhom : f.IsHomogeneous k := by simpa using hf
  rw [MvPolynomial.coe_eval₂Hom, Foundations.Scheme.HomogeneousEvalMap.eval₂_mul_of_isHomogeneous hhom]
  congr 1
  exact RingHom.congr_fun (projectiveChart_unnormalized_map R n i) f

/-- Dehomogenization is also a right inverse on every actual chart fraction. -/
theorem polynomialToProjectiveChart_comp (n : ℕ) (i : Fin (n + 1)) :
    (polynomialToProjectiveChart R n i).comp (projectiveChartToPolynomial R n i) =
      RingHom.id (projectiveChartRing R n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projectiveGrading R n) (projectiveVariable_homogeneous R n i) x
  simpa only [RingHom.comp_apply, RingHom.id_apply, projectiveChartToPolynomial_mk] using
    polynomialToProjectiveChart_dehomogenize R n i k f hf

/-- The standard scheme chart ring is canonically the polynomial ring in all
homogeneous coordinate ratios except the normalized coordinate. -/
def projectiveChartRingEquiv (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing R n i ≃+* projectiveChartPolynomial R n i where
  toFun := projectiveChartToPolynomial R n i
  invFun := polynomialToProjectiveChart R n i
  left_inv x := RingHom.congr_fun (polynomialToProjectiveChart_comp R n i) x
  right_inv x := RingHom.congr_fun (projectiveChartToPolynomial_comp R n i) x
  map_add' := map_add (projectiveChartToPolynomial R n i)
  map_mul' := map_mul (projectiveChartToPolynomial R n i)

@[simp]
theorem projectiveChartRingEquiv_apply (n : ℕ) (i : Fin (n + 1))
    (x : projectiveChartRing R n i) :
    projectiveChartRingEquiv R n i x = projectiveChartToPolynomial R n i x := rfl

@[simp]
theorem projectiveChartRingEquiv_symm_apply (n : ℕ) (i : Fin (n + 1))
    (p : projectiveChartPolynomial R n i) :
    (projectiveChartRingEquiv R n i).symm p = polynomialToProjectiveChart R n i p := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMProjectiveCharts.ProjectiveCharts
