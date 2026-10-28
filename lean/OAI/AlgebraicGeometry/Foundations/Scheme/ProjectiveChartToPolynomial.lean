import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Projective Chart To Polynomial -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial

noncomputable section

/-!
# The actual standard Proj chart maps to its polynomial coordinate ring

This uses the homogeneous localization that occurs in mathlib's affine chart
isomorphism for `Proj`, rather than a separate model of projective points.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- The homogeneous localization defining the standard `i`-th Proj chart. -/
abbrev projectiveChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)

/-- The affine polynomial coordinate ring, omitting the `i`-th variable. -/
abbrev projectiveChartPolynomial (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial {j : Fin (n + 1) // j ≠ i} ℂ

theorem projectiveVariable_homogeneous (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ ProjectiveSpace.projectiveGrading n 1 :=
  MvPolynomial.isHomogeneous_X ℂ i

/-- Constant coefficients in the actual homogeneous chart ring. -/
def projectiveChartConstants (n : ℕ) (i : Fin (n + 1)) :
    ℂ →+* projectiveChartRing n i :=
  (HomogeneousLocalization.fromZeroRingHom (ProjectiveSpace.projectiveGrading n)
    (Submonoid.powers (MvPolynomial.X i))).comp (ProjectiveSpace.degreeZeroConstants n).toRingHom

/-- Setting `Xᵢ = 1` extends to the ordinary localization at `Xᵢ`. -/
def projectiveChartLocalizationToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) →+*
      projectiveChartPolynomial n i :=
  Localization.awayLift (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Dehomogenization restricted to the actual degree-zero localization. -/
def projectiveChartToPolynomial (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing n i →+* projectiveChartPolynomial n i :=
  (projectiveChartLocalizationToPolynomial n i).comp
    (algebraMap (projectiveChartRing n i)
      (Localization.Away (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n)))

/-- A homogeneous fraction `f / Xᵢ^k` maps exactly to `f(Xᵢ:= 1)`. -/
@[simp]
theorem projectiveChartToPolynomial_mk (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (f : ProjectiveSpace.homogeneousCoordinateRing n)
    (hf : f ∈ ProjectiveSpace.projectiveGrading n (k • (1 : ℕ))) :
    projectiveChartToPolynomial n i
      (HomogeneousLocalization.Away.mk (ProjectiveSpace.projectiveGrading n)
        (projectiveVariable_homogeneous n i) k f hf) = DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f := by
  change Localization.awayLift (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk f ⟨MvPolynomial.X i ^ k, k, rfl⟩) = _
  simpa using Localization.awayLift_mk (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) f 1 (by simp) k

/-- Dehomogenization preserves the coefficient homomorphism to the chart. -/
@[simp]
theorem projectiveChartToPolynomial_constants (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    projectiveChartToPolynomial n i (projectiveChartConstants n i c) =
      MvPolynomial.C c := by
  change Localization.awayLift (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk (MvPolynomial.C c) ⟨1, Submonoid.one_mem _⟩) = _
  simpa using Localization.awayLift_mk (DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) (MvPolynomial.C c) 1 (by simp) 0

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial
