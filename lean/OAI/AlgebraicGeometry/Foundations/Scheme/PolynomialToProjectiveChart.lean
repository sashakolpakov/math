import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial
import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap

/-! # Polynomial To Projective Chart -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.PolynomialToProjectiveChart

noncomputable section

/-!
# Polynomial coordinates are the actual homogeneous localization chart

Variables map to the degree-zero homogeneous fractions `X_j / X_i`. The inverse
identities use homogeneous polynomial evaluation in the ordinary localization,
so this comparison identifies actual rings used by the scheme `Proj`.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- A degree-zero coordinate fraction in the actual standard Proj chart. -/
def projectiveChartRatio (n : ℕ) (i j : Fin (n + 1)) : ProjectiveChartToPolynomial.projectiveChartRing n i :=
  HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
    (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) 1 (MvPolynomial.X j)
    (by simpa using ProjectiveChartToPolynomial.projectiveVariable_homogeneous n j)

@[simp]
theorem projectiveChartToPolynomial_ratio (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    ProjectiveChartToPolynomial.projectiveChartToPolynomial n i (projectiveChartRatio n i j.val) = X j := by
  simp [projectiveChartRatio, j.property]

/-- Map an affine polynomial into the homogeneous chart by coordinate ratios. -/
def polynomialToProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChartToPolynomial.projectiveChartPolynomial n i →+* ProjectiveChartToPolynomial.projectiveChartRing n i :=
  MvPolynomial.eval₂Hom (ProjectiveChartToPolynomial.projectiveChartConstants n i)
    (fun j => projectiveChartRatio n i j.val)

@[simp]
theorem polynomialToProjectiveChart_C (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    polynomialToProjectiveChart n i (C c) = ProjectiveChartToPolynomial.projectiveChartConstants n i c := by
  simp [polynomialToProjectiveChart]

@[simp]
theorem polynomialToProjectiveChart_X (n : ℕ) (i : Fin (n + 1))
    (j : {j : Fin (n + 1) // j ≠ i}) :
    polynomialToProjectiveChart n i (X j) = projectiveChartRatio n i j.val := by
  simp [polynomialToProjectiveChart]

/-- Substitution back to affine polynomials is a left inverse. -/
theorem projectiveChartToPolynomial_comp (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i).comp (polynomialToProjectiveChart n i) =
      RingHom.id (ProjectiveChartToPolynomial.projectiveChartPolynomial n i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- The constants in the homogeneous chart have their expected value in the
ordinary localization. -/
@[simp]
theorem projectiveChartConstants_val (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    (ProjectiveChartToPolynomial.projectiveChartConstants n i c).val =
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- Coordinate fractions have their expected value in the ordinary localization. -/
theorem projectiveChartRatio_val (n : ℕ) (i j : Fin (n + 1)) :
    (projectiveChartRatio n i j).val =
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) := by
  simp only [projectiveChartRatio, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- General homogeneous chart fractions have the expected inverse-power denominator. -/
theorem projectiveChartFraction_val (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    (HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) k f hf).val =
      IsLocalization.Away.invSelf (S := Localization.Away
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) ^ k *
      algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) f := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  congr 1
  simpa only [one_pow, SubmonoidClass.mk_pow, IsLocalization.Away.invSelf] using
    (IsLocalization.mk'_pow
      (S := Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))
      (1 : ProjectiveSpace.homogeneousCoordinateRing n)
      (⟨MvPolynomial.X i, Submonoid.mem_powers _⟩ :
        Submonoid.powers (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) k)

/-- Substitution by ratios in the ordinary localization is normalization of
all homogeneous variables by the same inverse of `X_i`. -/
theorem projectiveChart_normalization_map (n : ℕ) (i : Fin (n + 1)) :
    ((algebraMap (ProjectiveChartToPolynomial.projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp
      (polynomialToProjectiveChart n i)).comp (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) =
    MvPolynomial.eval₂Hom
      ((algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp C)
      (fun j => IsLocalization.Away.invSelf
        (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) *
        algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
          (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [RingHom.comp_apply, DehomogenizationC.Algebraic.Dehomogenization.dehomogenize_X_self, map_one, eval₂Hom_X']
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp [hj, projectiveChartRatio_val, mul_comm]

/-- Evaluation of all original variables through their localization images
is the localization homomorphism itself. -/
theorem projectiveChart_unnormalized_map (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.eval₂Hom
      ((algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp C)
      (fun j => algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
        (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) (X j)) =
    algebraMap (ProjectiveSpace.homogeneousCoordinateRing n)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    simp

/-- Every homogeneous chart fraction is the polynomial in coordinate ratios
obtained by dehomogenizing its numerator. -/
theorem polynomialToProjectiveChart_dehomogenize (n : ℕ) (i : Fin (n + 1)) (k : ℕ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    polynomialToProjectiveChart n i (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f) =
      HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) k f hf := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
  change (((algebraMap (ProjectiveChartToPolynomial.projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n))).comp
      (polynomialToProjectiveChart n i)).comp (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)) f = _
  rw [projectiveChart_normalization_map, projectiveChartFraction_val]
  have hhom : f.IsHomogeneous k := by simpa using hf
  rw [MvPolynomial.coe_eval₂Hom, HomogeneousEvalMap.eval₂_mul_of_isHomogeneous hhom]
  congr 1
  exact RingHom.congr_fun (projectiveChart_unnormalized_map n i) f

/-- Dehomogenization is also a right inverse on every actual chart fraction. -/
theorem polynomialToProjectiveChart_comp (n : ℕ) (i : Fin (n + 1)) :
    (polynomialToProjectiveChart n i).comp (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i) =
      RingHom.id (ProjectiveChartToPolynomial.projectiveChartRing n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (ProjectiveSpace.projectiveGrading n) (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) x
  simpa only [RingHom.comp_apply, RingHom.id_apply, ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk] using
    polynomialToProjectiveChart_dehomogenize n i k f hf

/-- The standard scheme chart ring is canonically the polynomial ring in all
homogeneous coordinate ratios except the normalized coordinate. -/
def projectiveChartRingEquiv (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveChartToPolynomial.projectiveChartRing n i ≃+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i where
  toFun := ProjectiveChartToPolynomial.projectiveChartToPolynomial n i
  invFun := polynomialToProjectiveChart n i
  left_inv x := RingHom.congr_fun (polynomialToProjectiveChart_comp n i) x
  right_inv x := RingHom.congr_fun (projectiveChartToPolynomial_comp n i) x
  map_add' := map_add (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)
  map_mul' := map_mul (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)

@[simp]
theorem projectiveChartRingEquiv_apply (n : ℕ) (i : Fin (n + 1))
    (x : ProjectiveChartToPolynomial.projectiveChartRing n i) :
    projectiveChartRingEquiv n i x = ProjectiveChartToPolynomial.projectiveChartToPolynomial n i x := rfl

@[simp]
theorem projectiveChartRingEquiv_symm_apply (n : ℕ) (i : Fin (n + 1))
    (p : ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :
    (projectiveChartRingEquiv n i).symm p = polynomialToProjectiveChart n i p := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.PolynomialToProjectiveChart
