import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Chart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective

/-! # Projective -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Projective.Grassmannian

noncomputable section

/-!
The projective scheme cut out by the homogeneous Plücker ideal, with its
standard affine charts and its closed embedding into projective space.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u})

def pluckerProjectiveScheme : Scheme.{u} :=
  Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotient (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))

def pluckerProjectiveOver : Over (Spec R) :=
  Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap
    (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))))

def pluckerProjectiveInclusion : pluckerProjectiveScheme (ι := ι) (ν := ν) R ⟶
    Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ι → ν) R) :=
  Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))

instance pluckerProjectiveInclusion_isClosedImmersion :
    IsClosedImmersion (pluckerProjectiveInclusion (ι := ι) (ν := ν) R) :=
  Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion_isClosedImmersion (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))

instance pluckerProjectiveOver_isProper [Finite ν] : IsProper (pluckerProjectiveOver (ι := ι) (ν := ν) R).hom :=
  Polynomial.Projective.PolynomialProjective.projectiveQuotient_proper (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))

variable (a : ι → ν)

def pluckerProjectiveChartMap : Chart.Grassmannian.pluckerChartScheme R a ⟶ pluckerProjectiveOver (ι := ι) (ν := ν) R := by
  let I := Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)
  let h := (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R a)
  let g := Proj.awayι (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X a)) h Nat.zero_lt_one
  exact Over.homMk g (Projective.Flatness.GradedHilbert.projectiveStructureMap_away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) h)

instance pluckerProjectiveChartMap_isOpenImmersion : IsOpenImmersion (pluckerProjectiveChartMap R a).left := by
  change IsOpenImmersion (Proj.awayι _ _ _ _)
  infer_instance

theorem pluckerProjectiveCharts_cover (x : pluckerProjectiveScheme (ι := ι) (ν := ν) R) :
    ∃ a : ι → ν, ∃ y : (Chart.Grassmannian.pluckerChartScheme R a).left, (pluckerProjectiveChartMap R a).left y = x := by
  obtain ⟨a, y, hy⟩ :=
    (Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))).openCover.exists_eq x
  exact ⟨a, y, hy⟩

def normalizedChartToPlucker : Normalized.Chart.Grassmannian.normalizedChart a (Spec R) ⟶ pluckerProjectiveOver (ι := ι) (ν := ν) R :=
  (Chart.Grassmannian.pluckerChartSchemeIso R a).inv ≫ pluckerProjectiveChartMap R a

instance normalizedChartToPlucker_isOpenImmersion : IsOpenImmersion (normalizedChartToPlucker R a).left := by
  have : IsIso (Chart.Grassmannian.pluckerChartSchemeIso R a).inv.left :=
    ((Over.forget (Spec R)).mapIso (Chart.Grassmannian.pluckerChartSchemeIso R a)).isIso_inv
  change IsOpenImmersion ((Chart.Grassmannian.pluckerChartSchemeIso R a).inv.left ≫ (pluckerProjectiveChartMap R a).left)
  infer_instance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Projective.Grassmannian
