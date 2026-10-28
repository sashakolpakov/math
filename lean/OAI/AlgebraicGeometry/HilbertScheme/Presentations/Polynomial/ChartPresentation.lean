import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Chart Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective

noncomputable section

/-!
The standard projective chart of a homogeneous quotient has the concrete
affine presentation obtained by adding the equation X_i = 1. This ring
presentation is suitable for arbitrary coefficient-ring base change.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}

def affineChartIdeal (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    Ideal (MvPolynomial σ R) := I.toIdeal ⊔ Ideal.span {X i - 1}

def affineChartMap (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    MvPolynomial σ R →+*
      HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) :=
  (HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i)).comp (Dehomogenization.PolynomialProjective.dehomogenize i)

theorem affineChartMap_homogeneous (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R))
    (i : σ) {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    affineChartMap I i f = HomogeneousLocalization.Away.mk (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)
      ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) d (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I f)
      (by rw [smul_eq_mul, mul_one]; exact ⟨f, hf, rfl⟩) := by
  change HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i) (Dehomogenization.PolynomialProjective.dehomogenize i f) = _
  rw [Dehomogenization.PolynomialProjective.dehomogenize_homogeneous i hf]
  erw [Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.map_mk]

theorem affineChartMap_surjective (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    Function.Surjective (affineChartMap I i) :=
  (Homogeneous.ProjectiveQuotient.HomogeneousQuotient.quotient_away_map_surjective I (X i) (isHomogeneous_X R i)).comp (Dehomogenization.PolynomialProjective.dehomogenize_surjective i)

theorem affineChartIdeal_le_kernel (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    affineChartIdeal I i ≤ RingHom.ker (affineChartMap I i) := by
  apply sup_le
  · intro f hf
    classical
    change affineChartMap I i f = 0
    rw [← DirectSum.sum_support_decompose (Dehomogenization.PolynomialProjective.polynomialGrading σ R) f, map_sum]
    apply Finset.sum_eq_zero
    intro d _hd
    rw [affineChartMap_homogeneous I i (DirectSum.decompose (Dehomogenization.PolynomialProjective.polynomialGrading σ R) f d).property]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
    have hz : Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I ((DirectSum.decompose (Dehomogenization.PolynomialProjective.polynomialGrading σ R) f d).val) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.isHomogeneous d hf)
    simp only [hz, Localization.mk_zero]
  · apply Ideal.span_le.mpr
    rintro f (rfl : f = X i - 1)
    change affineChartMap I i (X i - 1) = 0
    simp only [affineChartMap, RingHom.comp_apply, map_sub, map_one, Dehomogenization.PolynomialProjective.dehomogenize_self, sub_self]

def affineChartFactor (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    (MvPolynomial σ R ⧸ I.toIdeal) →+* (MvPolynomial σ R ⧸ affineChartIdeal I i) :=
  Ideal.Quotient.factor le_sup_left

theorem affineChartFactor_variable (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    affineChartFactor I i (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) = 1 := by
  change Ideal.Quotient.mk (affineChartIdeal I i) (X i) = 1
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (affineChartIdeal I i)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (show Ideal.span {X i - 1} ≤ affineChartIdeal I i from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton (X i - 1)))

def affineChartInverse (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) →+*
      MvPolynomial σ R ⧸ affineChartIdeal I i :=
  (Localization.awayLift (affineChartFactor I i) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
    (isUnit_iff_exists_inv.mpr ⟨1, by rw [affineChartFactor_variable, one_mul]⟩)).comp
      (algebraMap _ _)

theorem affineChartInverse_homogeneous (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R))
    (i : σ) {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    affineChartInverse I i (affineChartMap I i f) = Ideal.Quotient.mk (affineChartIdeal I i) f := by
  change (Localization.awayLift (affineChartFactor I i) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
      (isUnit_iff_exists_inv.mpr ⟨1, by rw [affineChartFactor_variable, one_mul]⟩))
    (HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i) (Dehomogenization.PolynomialProjective.dehomogenize i f)).val = _
  rw [Dehomogenization.PolynomialProjective.dehomogenize_homogeneous i hf]
  erw [Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.map_mk,
    HomogeneousLocalization.Away.val_mk,
    Localization.awayLift_mk (affineChartFactor I i) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
      (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I f) 1 (by rw [affineChartFactor_variable, one_mul]) d]
  simp only [one_pow, mul_one]
  rfl

theorem affineChartInverse_comp (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    (affineChartInverse I i).comp (affineChartMap I i) = Ideal.Quotient.mk (affineChartIdeal I i) := by
  ext x
  · exact affineChartInverse_homogeneous I i (isHomogeneous_C _ x)
  · exact affineChartInverse_homogeneous I i (isHomogeneous_X R x)

theorem affineChartMap_kernel (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
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
def affineChartPresentationEquiv (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    (MvPolynomial σ R ⧸ affineChartIdeal I i) ≃+*
      HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) :=
  (Ideal.quotEquivOfEq (affineChartMap_kernel I i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (affineChartMap_surjective I i))

theorem affineChartPresentationEquiv_mk (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R))
    (i : σ) (f : MvPolynomial σ R) :
    affineChartPresentationEquiv I i (Ideal.Quotient.mk (affineChartIdeal I i) f) =
      affineChartMap I i f := rfl

theorem affineChartMap_C (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) (r : R) :
    affineChartMap I i (C r) =
      algebraMap R (HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))) r := by
  change HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i) (Dehomogenization.PolynomialProjective.dehomogenize i (C r)) = _
  rw [Dehomogenization.PolynomialProjective.dehomogenize_homogeneous i (isHomogeneous_C _ r)]
  erw [Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, Algebra.algebraMap_eq_smul_one,
    HomogeneousLocalization.val_smul, HomogeneousLocalization.val_one]
  change Localization.mk (Ideal.Quotient.mk I.toIdeal (C r)) 1 =
    r • (1 : Localization.Away (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)))
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one, Algebra.smul_def, mul_one]
  exact (IsScalarTower.algebraMap_apply R (MvPolynomial σ R ⧸ I.toIdeal)
    (Localization.Away (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))) r).symm

def affineChartPresentationAlgEquiv (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) :
    (MvPolynomial σ R ⧸ affineChartIdeal I i) ≃ₐ[R]
      HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) where
  __ := affineChartPresentationEquiv I i
  commutes' r := affineChartMap_C I i r

theorem affineChartPresentationAlgEquiv_mk (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R))
    (i : σ) (f : MvPolynomial σ R) :
    affineChartPresentationAlgEquiv I i (Ideal.Quotient.mk (affineChartIdeal I i) f) =
      affineChartMap I i f := rfl

theorem affineChartPresentationAlgEquiv_symm_map (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R))
    (i : σ) (f : MvPolynomial σ R) :
    (affineChartPresentationAlgEquiv I i).symm (affineChartMap I i f) =
      Ideal.Quotient.mk (affineChartIdeal I i) f := by
  rw [← affineChartPresentationAlgEquiv_mk]
  exact (affineChartPresentationAlgEquiv I i).symm_apply_apply _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective
