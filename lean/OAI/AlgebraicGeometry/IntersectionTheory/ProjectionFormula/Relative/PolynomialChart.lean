import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap

/-! # Polynomial Chart -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PolynomialChart

noncomputable section

/-!
# Polynomial coordinates are the actual homogeneous localization chart

Variables map to the degree-zero homogeneous fractions `X_j / X_i`. The inverse
identities use homogeneous polynomial evaluation in the ordinary localization,
so this comparison identifies actual rings used by the scheme `Proj`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Projective

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (grading)

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- A degree-zero coordinate fraction in the actual standard Proj chart. -/
def projectiveChartRatio (R : Type) [CommRing R] (n : ℕ) (i j : Fin (n + 1)) : ProjectiveChart.projectiveChartRing R n i :=
  HomogeneousLocalization.Away.mk (ProjectiveLinear.grading R n)
    (ProjectiveChart.projectiveVariable_homogeneous R n i) 1 (MvPolynomial.X j)
    (by simpa using ProjectiveChart.projectiveVariable_homogeneous R n j)

@[simp]
theorem projectiveChartToPolynomial_ratio (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    ProjectiveChart.projectiveChartToPolynomial R n i (projectiveChartRatio R n i j.val) = X j := by
  simp [projectiveChartRatio, j.property]

/-- Map an affine polynomial into the homogeneous chart by coordinate ratios. -/
def polynomialToProjectiveChart (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChart.projectiveChartPolynomial R n i →+* ProjectiveChart.projectiveChartRing R n i :=
  MvPolynomial.eval₂Hom (ProjectiveChart.projectiveChartConstants R n i)
    (fun j => projectiveChartRatio R n i j.val)

@[simp]
theorem polynomialToProjectiveChart_C (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (c : R) :
    polynomialToProjectiveChart R n i (C c) = ProjectiveChart.projectiveChartConstants R n i c := by
  simp [polynomialToProjectiveChart]

@[simp]
theorem polynomialToProjectiveChart_X (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    polynomialToProjectiveChart R n i (X j) = projectiveChartRatio R n i j.val := by
  simp [polynomialToProjectiveChart]

/-- Substitution back to affine polynomials is a left inverse. -/
theorem projectiveChartToPolynomial_comp (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveChart.projectiveChartToPolynomial R n i).comp (polynomialToProjectiveChart R n i) =
      RingHom.id (ProjectiveChart.projectiveChartPolynomial R n i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- The constants in the homogeneous chart have their expected value in the
ordinary localization. -/
@[simp]
theorem projectiveChartConstants_val (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (c : R) :
    (ProjectiveChart.projectiveChartConstants R n i c).val =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Coordinate fractions have their expected value in the ordinary localization. -/
theorem projectiveChartRatio_val (R : Type) [CommRing R] (n : ℕ) (i j : Fin (n + 1)) :
    (projectiveChartRatio R n i j).val =
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) := by
  simp only [projectiveChartRatio, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- General homogeneous chart fractions have the expected inverse-power denominator. -/
theorem projectiveChartFraction_val (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ ProjectiveLinear.grading R n (k • (1 : ℕ))) :
    (HomogeneousLocalization.Away.mk (ProjectiveLinear.grading R n)
      (ProjectiveChart.projectiveVariable_homogeneous R n i) k f hf).val =
      IsLocalization.Away.invSelf (S := Localization.Away
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ^ k *
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) f := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  simpa only [one_pow, SubmonoidClass.mk_pow, IsLocalization.Away.invSelf] using
    (IsLocalization.mk'_pow
      (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
      (1 : MvPolynomial (Fin (n + 1)) R)
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) k)

/-- Substitution by ratios in the ordinary localization is normalization of
all homogeneous variables by the same inverse of `X_i`. -/
theorem projectiveChart_normalization_map (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    ((algebraMap (ProjectiveChart.projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))).comp
      (polynomialToProjectiveChart R n i)).comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) =
    MvPolynomial.eval₂Hom
      ((algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))).comp C)
      (fun j => IsLocalization.Away.invSelf
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) *
        algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (X j)) := by
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
theorem projectiveChart_unnormalized_map (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.eval₂Hom
      ((algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))).comp C)
      (fun j => algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (X j)) =
    algebraMap (MvPolynomial (Fin (n + 1)) R)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- Every homogeneous chart fraction is the polynomial in coordinate ratios
obtained by dehomogenizing its numerator. -/
theorem polynomialToProjectiveChart_dehomogenize (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f ∈ ProjectiveLinear.grading R n (k • (1 : ℕ))) :
    polynomialToProjectiveChart R n i (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f) =
      HomogeneousLocalization.Away.mk (ProjectiveLinear.grading R n)
        (ProjectiveChart.projectiveVariable_homogeneous R n i) k f hf := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  change (((algebraMap (ProjectiveChart.projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))).comp
      (polynomialToProjectiveChart R n i)).comp (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)) f = _
  rw [projectiveChart_normalization_map, projectiveChartFraction_val]
  have hhom : f.IsHomogeneous k := by simpa using hf
  rw [MvPolynomial.coe_eval₂Hom, Foundations.Scheme.HomogeneousEvalMap.eval₂_mul_of_isHomogeneous hhom]
  congr 1
  exact RingHom.congr_fun (projectiveChart_unnormalized_map R n i) f

/-- Dehomogenization is also a right inverse on every actual chart fraction. -/
theorem polynomialToProjectiveChart_comp (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (polynomialToProjectiveChart R n i).comp (ProjectiveChart.projectiveChartToPolynomial R n i) =
      RingHom.id (ProjectiveChart.projectiveChartRing R n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (ProjectiveLinear.grading R n) (ProjectiveChart.projectiveVariable_homogeneous R n i) x
  simpa only [RingHom.comp_apply, RingHom.id_apply, ProjectiveChart.projectiveChartToPolynomial_mk] using
    polynomialToProjectiveChart_dehomogenize R n i k f hf

/-- The standard scheme chart ring is canonically the polynomial ring in all
homogeneous coordinate ratios except the normalized coordinate. -/
def projectiveChartRingEquiv (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChart.projectiveChartRing R n i ≃+* ProjectiveChart.projectiveChartPolynomial R n i where
  toFun := ProjectiveChart.projectiveChartToPolynomial R n i
  invFun := polynomialToProjectiveChart R n i
  left_inv x := RingHom.congr_fun (polynomialToProjectiveChart_comp R n i) x
  right_inv x := RingHom.congr_fun (projectiveChartToPolynomial_comp R n i) x
  map_add' := map_add (ProjectiveChart.projectiveChartToPolynomial R n i)
  map_mul' := map_mul (ProjectiveChart.projectiveChartToPolynomial R n i)

@[simp]
theorem projectiveChartRingEquiv_apply (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (x : ProjectiveChart.projectiveChartRing R n i) :
    projectiveChartRingEquiv R n i x = ProjectiveChart.projectiveChartToPolynomial R n i x := rfl

@[simp]
theorem projectiveChartRingEquiv_symm_apply (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (p : ProjectiveChart.projectiveChartPolynomial R n i) :
    (projectiveChartRingEquiv R n i).symm p = polynomialToProjectiveChart R n i p := rfl

end Projective

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.PolynomialChart
