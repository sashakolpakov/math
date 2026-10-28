import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Chart Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPresentation.GradedHilbert

noncomputable section

/-!
The standard projective chart of a homogeneous quotient has the concrete
affine presentation obtained by adding the equation X_i = 1. This ring
presentation is suitable for arbitrary coefficient-ring base change.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def affineChartIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) := I.toIdeal ⊔ Ideal.span {X i - 1}

def affineChartMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R n →+*
      HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) :=
  (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)).comp (Dehomogenization.GradedHilbert.dehomogenize i)

theorem affineChartMap_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    affineChartMap I i f = HomogeneousLocalization.Away.mk (Graded.Quotient.GradedHilbert.quotientGrading I)
      ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) d (Graded.Quotient.GradedHilbert.gradedQuotientMap I f)
      (by rw [smul_eq_mul, mul_one]; exact ⟨f, hf, rfl⟩) := by
  change HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i) (Dehomogenization.GradedHilbert.dehomogenize i f) = _
  rw [Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf]
  erw [Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.map_mk]

theorem affineChartMap_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    Function.Surjective (affineChartMap I i) :=
  (Projective.Quotient.GradedHilbert.quotient_away_map_surjective I (X i) (isHomogeneous_X R i)).comp (Dehomogenization.GradedHilbert.dehomogenize_surjective i)

theorem affineChartIdeal_le_kernel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    affineChartIdeal I i ≤ RingHom.ker (affineChartMap I i) := by
  apply sup_le
  · intro f hf
    change Dehomogenization.GradedHilbert.dehomogenize i f ∈ RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i))
    rw [Projective.IdealEquivalence.GradedHilbert.quotient_chart_kernel_eq_map]
    exact Ideal.mem_map_of_mem _ hf
  · apply Ideal.span_le.mpr
    rintro f (rfl : f = X i - 1)
    change affineChartMap I i (X i - 1) = 0
    simp only [affineChartMap, RingHom.comp_apply, map_sub, map_one, Dehomogenization.GradedHilbert.dehomogenize_self, sub_self]

def affineChartFactor (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) →+* (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ affineChartIdeal I i) :=
  Ideal.Quotient.factor le_sup_left

theorem affineChartFactor_variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    affineChartFactor I i (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) = 1 := by
  change Ideal.Quotient.mk (affineChartIdeal I i) (X i) = 1
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (affineChartIdeal I i)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (show Ideal.span {X i - 1} ≤ affineChartIdeal I i from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton (X i - 1)))

def affineChartInverse (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) →+*
      Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ affineChartIdeal I i :=
  (Localization.awayLift (affineChartFactor I i) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [affineChartFactor_variable, one_mul]⟩)).comp
      (algebraMap _ _)

theorem affineChartInverse_homogeneous (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    affineChartInverse I i (affineChartMap I i f) = Ideal.Quotient.mk (affineChartIdeal I i) f := by
  change (Localization.awayLift (affineChartFactor I i) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      (isUnit_iff_exists_inv.mpr ⟨1, by rw [affineChartFactor_variable, one_mul]⟩))
    (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i) (Dehomogenization.GradedHilbert.dehomogenize i f)).val = _
  rw [Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf]
  erw [Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.map_mk,
    HomogeneousLocalization.Away.val_mk,
    Localization.awayLift_mk (affineChartFactor I i) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      (Graded.Quotient.GradedHilbert.gradedQuotientMap I f) 1 (by rw [affineChartFactor_variable, one_mul]) d]
  simp only [one_pow, mul_one]
  rfl

theorem affineChartInverse_comp (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    (affineChartInverse I i).comp (affineChartMap I i) = Ideal.Quotient.mk (affineChartIdeal I i) := by
  ext x
  · exact affineChartInverse_homogeneous I i (isHomogeneous_C _ x)
  · exact affineChartInverse_homogeneous I i (isHomogeneous_X R x)

theorem affineChartMap_kernel (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    RingHom.ker (affineChartMap I i) = affineChartIdeal I i := by
  apply le_antisymm
  · intro f hf
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← affineChartInverse_comp I i]
    change affineChartInverse I i (affineChartMap I i f) = 0
    rw [show affineChartMap I i f = 0 from hf, map_zero]
  · exact affineChartIdeal_le_kernel I i

/-- The usual affine chart presentation, valid for every commutative
coefficient ring and every homogeneous ideal. -/
def affineChartPresentationEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ affineChartIdeal I i) ≃+*
      HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) :=
  (Ideal.quotEquivOfEq (affineChartMap_kernel I i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (affineChartMap_surjective I i))

theorem affineChartPresentationEquiv_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    affineChartPresentationEquiv I i (Ideal.Quotient.mk (affineChartIdeal I i) f) =
      affineChartMap I i f := rfl

theorem affineChartMap_C (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) (r : R) :
    affineChartMap I i (C r) =
      algebraMap R (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) r := by
  change HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i) (Dehomogenization.GradedHilbert.dehomogenize i (C r)) = _
  rw [Dehomogenization.GradedHilbert.dehomogenize_homogeneous i (isHomogeneous_C _ r)]
  erw [Projective.IdealRecovery.GradedHilbert.coordinateFraction, HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, Algebra.algebraMap_eq_smul_one,
    HomogeneousLocalization.val_smul, HomogeneousLocalization.val_one]
  change Localization.mk (Ideal.Quotient.mk I.toIdeal (C r)) 1 =
    r • (1 : Localization.Away (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)))
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one, Algebra.smul_def, mul_one]
  exact (IsScalarTower.algebraMap_apply R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (Localization.Away (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) r).symm

def affineChartPresentationAlgEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ affineChartIdeal I i) ≃ₐ[R]
      HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) where
  __ := affineChartPresentationEquiv I i
  commutes' r := affineChartMap_C I i r

theorem affineChartPresentationAlgEquiv_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    affineChartPresentationAlgEquiv I i (Ideal.Quotient.mk (affineChartIdeal I i) f) =
      affineChartMap I i f := rfl

theorem affineChartPresentationAlgEquiv_symm_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    (affineChartPresentationAlgEquiv I i).symm (affineChartMap I i f) =
      Ideal.Quotient.mk (affineChartIdeal I i) f := by
  rw [← affineChartPresentationAlgEquiv_mk]
  exact (affineChartPresentationAlgEquiv I i).symm_apply_apply _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPresentation.GradedHilbert
