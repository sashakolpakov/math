import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DehomogenizationKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation

/-! # Homogenized Affine Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedAffineChart.PolynomialHomogenization

noncomputable section

/-! The distinguished chart of a homogenized polynomial quotient recovers its affine presentation. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective

variable {R σ κ : Type*} [CommRing R]

def affineRelationEvaluation (g : κ → MvPolynomial σ R) :
    MvPolynomial (Option σ) R →ₐ[R] (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) where
  __ := (Ideal.Quotient.mk (Ideal.span (Set.range g))).comp (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R)
  commutes' r := by
    change Ideal.Quotient.mk (Ideal.span (Set.range g)) (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R (C r)) =
      Ideal.Quotient.mk (Ideal.span (Set.range g)) (C r)
    rw [Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption_C]

theorem affineRelationEvaluation_surjective (g : κ → MvPolynomial σ R) :
    Function.Surjective (affineRelationEvaluation g) := by
  change Function.Surjective
    ((Ideal.Quotient.mk (Ideal.span (Set.range g))).comp (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R))
  exact (Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range g))).comp
    Polynomial.DehomogenizationKernel.PolynomialHomogenization.dehomogenizeOption_surjective

theorem affineRelationEvaluation_kernel (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    RingHom.ker (affineRelationEvaluation g).toRingHom =
      HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none := by
  have h : RingHom.ker (affineRelationEvaluation g).toRingHom =
      Ideal.comap (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R) (Ideal.span (Set.range g)) := by
    ext p
    change Ideal.Quotient.mk (Ideal.span (Set.range g)) (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R p) = 0 ↔
      Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R p ∈ Ideal.span (Set.range g)
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [h, ← Polynomial.Homogenization.PolynomialHomogenization.map_dehomogenizeOption_homogenizedIdeal g d hd,
    Polynomial.DehomogenizationKernel.PolynomialHomogenization.dehomogenizeOption_comap_map]
  rfl

def affineRelationQuotientEquiv (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    (MvPolynomial (Option σ) R ⧸ HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartIdeal (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none) ≃ₐ[R]
      (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) :=
  (Ideal.quotientEquivAlgOfEq R (affineRelationEvaluation_kernel g d hd).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (affineRelationEvaluation_surjective g))

def homogenizedAffineChartEquiv (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    Away (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d))
      (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) (X none)) ≃ₐ[R]
        (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) :=
  (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none).symm.trans
    (affineRelationQuotientEquiv g d hd)

theorem homogenizedAffineChartEquiv_map (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) (p : MvPolynomial (Option σ) R) :
    homogenizedAffineChartEquiv g d hd (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none p) =
      Ideal.Quotient.mk (Ideal.span (Set.range g)) (Polynomial.Homogenization.PolynomialHomogenization.dehomogenizeOption R p) := by
  change affineRelationQuotientEquiv g d hd
    ((HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none).symm
      (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) none p)) = _
  rw [HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartPresentationAlgEquiv_symm_map]
  dsimp only [affineRelationQuotientEquiv]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedAffineChart.PolynomialHomogenization
