import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedAffineChart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective

/-! # Homogenized Projective Closure -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedProjectiveClosure.PolynomialHomogenization

noncomputable section

/-! Actual proper projective closures, with an open chart recovering the affine relation quotient. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective

universe u

variable {R σ : Type u} {κ : Type*} [CommRing R]

abbrev homogenizedProjectiveClosure (g : κ → MvPolynomial σ R) (d : κ → ℕ) : Scheme.{u} :=
  Proj (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d))

def homogenizedProjectiveBase (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProjectiveClosure g d ⟶ Spec (.of R) :=
  HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d))

theorem homogenizedProjectiveBase_proper [Finite σ]
    (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsProper (homogenizedProjectiveBase g d) :=
  HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotient_proper (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d)

def homogenizedProjectiveEmbedding (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProjectiveClosure g d ⟶ Proj (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Option σ) R) :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d)

theorem homogenizedProjectiveEmbedding_closed (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    IsClosedImmersion (homogenizedProjectiveEmbedding g d) :=
  HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion_isClosedImmersion (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d)

theorem homogenizedProjectiveEmbedding_over (g : κ → MvPolynomial σ R) (d : κ → ℕ) :
    homogenizedProjectiveEmbedding g d ≫
      HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Option σ) R) =
        homogenizedProjectiveBase g d :=
  HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientInclusion_over (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d)

def homogenizedAffineOpen (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    Spec (.of (MvPolynomial σ R ⧸ Ideal.span (Set.range g))) ⟶
      homogenizedProjectiveClosure g d :=
  Spec.map (HomogenizedAffineChart.PolynomialHomogenization.homogenizedAffineChartEquiv g d hd).toRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d))
      (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d) (X none))
      ((HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Polynomial.Homogenization.PolynomialHomogenization.homogenizedIdeal g d)).map_mem (isHomogeneous_X R none))
      Nat.zero_lt_one

theorem homogenizedAffineOpen_isOpenImmersion (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    IsOpenImmersion (homogenizedAffineOpen g d hd) := by
  have : IsIso (HomogenizedAffineChart.PolynomialHomogenization.homogenizedAffineChartEquiv g d hd).toRingEquiv.toCommRingCatIso.hom :=
    (HomogenizedAffineChart.PolynomialHomogenization.homogenizedAffineChartEquiv g d hd).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold homogenizedAffineOpen
  infer_instance

theorem homogenizedAffineOpen_over (g : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hd : ∀ i, (g i).totalDegree ≤ d i) :
    homogenizedAffineOpen g d hd ≫ homogenizedProjectiveBase g d =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)))) := by
  unfold homogenizedAffineOpen homogenizedProjectiveBase
  rw [Category.assoc, HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap_away,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (HomogenizedAffineChart.PolynomialHomogenization.homogenizedAffineChartEquiv g d hd).toAlgHom.comp_algebraMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedProjectiveClosure.PolynomialHomogenization
