import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SingletonChartRingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.SectionFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartEvaluation

/-! # Quotient Coordinate Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientCoordinateChart

noncomputable section

/-! The actual quotient inclusion on a standard open is the normalized
projective chart map of its canonical coordinate-section ratios. Its
coefficient map is the original structural coefficient map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateSectionChartValues (i j : Fin (n + 1)) :
    Γ((ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).toScheme, ⊤) :=
  (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).topIso.inv
    (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i))

theorem coordinateSectionChartValues_pivot (i : Fin (n + 1)) : coordinateSectionChartValues I i i = 1 := by
  unfold coordinateSectionChartValues
  rw [Coordinate.RatioSections.coordinateRatioSection_self, map_one]

def coordinateSectionChartCoefficients (i : Fin (n + 1)) :
    R →+* Γ((ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).toScheme, ⊤) :=
  ((ProjectiveChart.GlobalSectionMap.projectiveChartGlobalSectionMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}))).comp
    (Coordinate.SingletonChartRingMap.coordinateSingletonChartRingMap I i)).comp (algebraMap R (ProjectiveChart.Evaluation.projectiveChartRing R n i))

theorem projectiveQuotientInclusion_coordinateChart (i : Fin (n + 1)) :
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      ProjectiveChart.Evaluation.projectiveChartMap (coordinateSectionChartCoefficients I i) (coordinateSectionChartValues I i) i
        (coordinateSectionChartValues_pivot I i) := by
  let Q := HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I
  let g := HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I
  let hg := HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I
  let f := g (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i})
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  have hf : f ∈ Q 1 := by
    have hh := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I {i}
    simp only [Finset.card_singleton] at hh
    exact hh
  let a := Segre.StandardChartRingMap.homogeneousAwayEquivOfEq Q (Coordinate.SingletonChartRingMap.coordinateSingletonDenominator_eq I i)
  let ψ := ProjectiveChart.GlobalSectionMap.projectiveChartGlobalSectionMap Q f
  let φ := ψ.comp a.toRingHom
  have hC (r : R) : φ (HomogeneousLocalization.Away.map g (X i)
      (algebraMap R (ProjectiveChart.Evaluation.projectiveChartRing R n i) r)) = coordinateSectionChartCoefficients I i r := rfl
  have hX (j : Fin (n + 1)) : φ (HomogeneousLocalization.Away.map g (X i)
      (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j))) = coordinateSectionChartValues I i j := by
    change ProjectiveChart.GlobalSectionMap.projectiveChartGlobalSectionMap Q f
      (Coordinate.SingletonChartRingMap.coordinateSingletonChartRingMap I i (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (X j))) = _
    rw [Coordinate.SingletonChartRingMap.coordinateSingletonChartRingMap_coordinate]
    rfl
  have hmap : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) :=
    Spec.map_comp (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom ψ)
  have hpoint : U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι Q (g (X i)) (g.map_mem (isHomogeneous_X R i)) Nat.zero_lt_one = U.ι := by
    rw [hmap, Category.assoc,
      Segre.StandardChartEvaluation.homogeneousAwayEquivOfEq_awayι Q (Coordinate.SingletonChartRingMap.coordinateSingletonDenominator_eq I i)
        (g.map_mem (isHomogeneous_X R i)) hf Nat.zero_lt_one]
    exact (Category.assoc _ _ _).symm.trans
      (ProjectiveChart.GlobalSectionMap.projectiveChartGlobalSectionMap_awayι Q f hf Nat.zero_lt_one)
  have h := ProjectiveChart.MapRecognition.projectiveMap_chart_of_coordinates Q g hg (coordinateSectionChartCoefficients I i)
    (coordinateSectionChartValues I i) i (coordinateSectionChartValues_pivot I i) φ hC hX
  exact (congrArg (fun k => k ≫ Proj.map g hg) hpoint).symm.trans h

theorem coordinateSectionChartCoefficients_structural (i : Fin (n + 1)) :
    coordinateSectionChartCoefficients I i =
      Coefficient.ModulePresheaf.schemeCoefficientMap ((ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := by
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  let c := coordinateSectionChartCoefficients I i
  let v := coordinateSectionChartValues I i
  let hv := coordinateSectionChartValues_pivot I i
  calc
    c = Coefficient.ModulePresheaf.schemeCoefficientMap (ProjectiveChart.Evaluation.projectiveChartMap c v i hv ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) :=
      (ProjectiveChart.CoefficientRecovery.projectiveChartMap_structural_coefficients c v i hv).symm
    _ = Coefficient.ModulePresheaf.schemeCoefficientMap ((U.ι ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) :=
      congrArg (fun k => Coefficient.ModulePresheaf.schemeCoefficientMap (k ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom))
        (projectiveQuotientInclusion_coordinateChart I i).symm
    _ = _ := by rw [Category.assoc, Projective.CoefficientPullback.projectiveQuotientInclusion_standard_over]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientCoordinateChart
