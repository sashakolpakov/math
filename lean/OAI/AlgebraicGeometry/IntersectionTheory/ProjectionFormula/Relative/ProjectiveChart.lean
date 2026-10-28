import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI
import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Projective Chart -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveChart

noncomputable section

/-!
# The actual standard Proj chart maps to its polynomial coordinate ring

This uses the homogeneous localization that occurs in mathlib's affine chart
isomorphism for `Proj`, rather than a separate model of projective points.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- The homogeneous localization defining the standard `i`-th Proj chart. -/
abbrev projectiveChartRing (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (ProjectiveLinear.grading R n) (MvPolynomial.X i)

/-- The affine polynomial coordinate ring, omitting the `i`-th variable. -/
abbrev projectiveChartPolynomial (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial {j : Fin (n + 1) // j ≠ i} R

theorem projectiveVariable_homogeneous (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ ProjectiveLinear.grading R n 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- Constant coefficients in the actual homogeneous chart ring. -/
def projectiveChartConstants (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    R →+* projectiveChartRing R n i :=
  (HomogeneousLocalization.fromZeroRingHom (ProjectiveLinear.grading R n)
    (Submonoid.powers (MvPolynomial.X i))).comp (ProjectiveI.Base.constants R n).toRingHom

/-- Setting `Xᵢ = 1` extends to the ordinary localization at `Xᵢ`. -/
def projectiveChartLocalizationToPolynomial (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →+*
      projectiveChartPolynomial R n i :=
  Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Dehomogenization restricted to the actual degree-zero localization. -/
def projectiveChartToPolynomial (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    projectiveChartRing R n i →+* projectiveChartPolynomial R n i :=
  (projectiveChartLocalizationToPolynomial R n i).comp
    (algebraMap (projectiveChartRing R n i)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))

/-- A homogeneous fraction `f / Xᵢ^k` maps exactly to `f(Xᵢ:= 1)`. -/
@[simp]
theorem projectiveChartToPolynomial_mk (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f ∈ ProjectiveLinear.grading R n (k • (1 : ℕ))) :
    projectiveChartToPolynomial R n i
      (HomogeneousLocalization.Away.mk (ProjectiveLinear.grading R n)
        (projectiveVariable_homogeneous R n i) k f hf) = Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f := by
  change Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk f ⟨MvPolynomial.X i ^ k, k, rfl⟩) = _
  simpa using Localization.awayLift_mk (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) f 1 (by simp) k

/-- Dehomogenization preserves the coefficient homomorphism to the chart. -/
@[simp]
theorem projectiveChartToPolynomial_constants (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (c : R) :
    projectiveChartToPolynomial R n i (projectiveChartConstants R n i c) =
      MvPolynomial.C c := by
  change Localization.awayLift (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) (MvPolynomial.X i) (by simp)
    (Localization.mk (MvPolynomial.C c) ⟨1, Submonoid.one_mem _⟩) = _
  simpa using Localization.awayLift_mk (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i)
    (MvPolynomial.X i) (MvPolynomial.C c) 1 (by simp) 0

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveChart
