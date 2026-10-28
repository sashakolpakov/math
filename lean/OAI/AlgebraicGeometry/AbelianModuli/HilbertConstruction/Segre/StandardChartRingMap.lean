import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardGradedMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.MapRecognition

/-! # Standard Chart Ring Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartRingMap

noncomputable section

/-! The actual homogeneous-localization map of the standard Segre graded
map agrees with the quotient chart map after the denominator is identified
with its matrix pivot. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def homogeneousAwayEquivOfEq {f g : A} (h : f = g) :
    HomogeneousLocalization.Away 𝒜 f ≃+* HomogeneousLocalization.Away 𝒜 g := by
  subst g
  exact RingEquiv.refl _

theorem homogeneousAwayEquivOfEq_mk {f g : A} (h : f = g) {d : ℕ}
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) :
    homogeneousAwayEquivOfEq 𝒜 h (HomogeneousLocalization.Away.mk 𝒜 hf k a ha) =
      HomogeneousLocalization.Away.mk 𝒜 hg k a ha := by
  subst g
  rfl

variable (R) {n m d : ℕ} (e : ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1)) (i : Fin (d + 1))

def segreStandardChartRingMap :
    ProjectiveChart.Evaluation.projectiveChartRing R d i →+* ProjectiveCharts.SegreHomogeneousChart R (e.symm i).1 (e.symm i).2 :=
  (homogeneousAwayEquivOfEq _ (StandardGradedMap.segreStandardGradedMap_variable R e i)).toRingHom.comp
    (HomogeneousLocalization.Away.map (StandardGradedMap.segreStandardGradedMap R e) (X i))

theorem segreStandardChartRingMap_homogeneous {f : Projective.ProjectivePresentations.coordinateRing R d} {k : ℕ}
    (hf : f.IsHomogeneous k) :
    segreStandardChartRingMap R e i (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i f) =
      HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (e.symm i) (MvPolynomial.rename e.symm f) := by
  rw [HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_homogeneous i hf]
  change homogeneousAwayEquivOfEq _ (StandardGradedMap.segreStandardGradedMap_variable R e i)
    (HomogeneousLocalization.Away.map (StandardGradedMap.segreStandardGradedMap R e) (X i)
      (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R d) (isHomogeneous_X R i)
        k f (by simpa only [smul_eq_mul, mul_one] using (show f ∈ Projective.ProjectivePresentations.coordinateGrading R d k from hf)))) = _
  rw [HomogeneousLocalization.Away.map_mk,
    homogeneousAwayEquivOfEq_mk _ _ _ (ChartCoordinates.segreVariable R (e.symm i)).property,
    HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous _ _ hf.rename_isHomogeneous]
  rfl

theorem segreStandardChartRingMap_polynomial (f : Projective.ProjectivePresentations.coordinateRing R d) :
    segreStandardChartRingMap R e i (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i f) =
      HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (e.symm i) (MvPolynomial.rename e.symm f) := by
  have h : (segreStandardChartRingMap R e i).comp (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i) =
      (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (e.symm i)).comp (MvPolynomial.rename e.symm).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact segreStandardChartRingMap_homogeneous R e i (isHomogeneous_C _ r)
    · intro j
      exact segreStandardChartRingMap_homogeneous R e i (isHomogeneous_X R j)
  exact RingHom.congr_fun h f

theorem segreStandardChartRingMap_coordinate (j : Fin (d + 1)) :
    segreStandardChartRingMap R e i (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) =
      ChartCoordinates.segreChartCoordinate R (e.symm i).1 (e.symm i).2 (e.symm j) := by
  rw [segreStandardChartRingMap_polynomial, MvPolynomial.rename_X]
  rfl

theorem segreStandardChartRingMap_constant (r : R) :
    segreStandardChartRingMap R e i (algebraMap R (ProjectiveChart.Evaluation.projectiveChartRing R d i) r) =
      algebraMap R (ProjectiveCharts.SegreHomogeneousChart R (e.symm i).1 (e.symm i).2) r := by
  rw [← ProjectiveChart.Algebra.projectiveChart_dehomogenize_constant i r, segreStandardChartRingMap_polynomial,
    MvPolynomial.rename_C, HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_C]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartRingMap
