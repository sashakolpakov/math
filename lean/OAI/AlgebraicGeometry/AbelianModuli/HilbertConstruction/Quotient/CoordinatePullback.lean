import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Transitions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Quotient

/-! # Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback

noncomputable section

/-! Coordinate ratios of a homogeneous projective quotient are the pullbacks of the ambient projective coordinate functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Quotient.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def projectiveCoordinateFunction (R : Type u) [CommRing R] {n : ℕ} (i j : Fin (n + 1)) :
    Γ(Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :=
  Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)
    (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) 1 (X j)
      (by change (X j : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n).IsHomogeneous 1; exact isHomogeneous_X R j))

variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveQuotient_coordinate_preimage (i : Fin (n + 1)) :
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) =
      ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} :=
  (Proj.map_preimage_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) (X i)).trans
    (ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_singleton I i).symm

theorem projectiveQuotient_coordinate_pullback (i j : Fin (n + 1))
    (h : ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ≤
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) h (projectiveCoordinateFunction R i j) =
      Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i) := by
  have hxi : X i ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n 1 := isHomogeneous_X R i
  have hxj : X j ∈ HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n (1 • (1 : ℕ)) := isHomogeneous_X R j
  have he := Proj.awayToSection_comp_appLE (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I)
    hxi
  have hv := ConcreteCategory.congr_hom he
    (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) hxi 1 (X j) hxj)
  change (Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) _).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) _
      (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)
        (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) hxi 1 (X j) hxj)) =
    Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      (HomogeneousLocalization.Away.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)
        (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) hxi 1 (X j) hxj)) at hv
  rw [HomogeneousLocalization.Away.map_mk] at hv
  have hm : algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) = HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i) :=
    congrArg (algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal))
      (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton R i)
  have ha : algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) ∈ HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1 := by
    rw [hm]
    exact (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxi
  let P (z : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1) : Prop := ∀ hz : Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val ≤
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).appLE (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i))
      (Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val) hz (projectiveCoordinateFunction R i j) =
      Proj.awayToSection (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.val
        (HomogeneousLocalization.Away.mk (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) z.property 1
          (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X j)) ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxj))
  have hp : P ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i), (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxi⟩ := by
    intro hz
    exact hv
  have hz : (⟨algebraMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i}), ha⟩ : HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I 1) =
      ⟨HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i), (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hxi⟩ := Subtype.ext hm
  have hp' := (congrArg P hz).mpr hp
  unfold Coordinate.RatioSections.coordinateRatioSection Coordinate.HomogeneousRatios.coordinateHomogeneousRatio Homogeneous.FactorRatios.homogeneousFactorRatio
  simp only [Finset.erase_singleton, HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.inversionMonomial_empty, map_one, mul_one, Finset.card_singleton]
  exact hp' h

theorem projectiveFrameRatio_from_singleton (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (i j : Fin (n + 1)) (hi : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
    (hj : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) :
    ProjectiveFrame.Ratios.projectiveFrameRatio I V i j hi hj =
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hi).op
        (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) := by
  have h : ({i} : Finset (Fin (n + 1))) ⊆ {i, j} := by
    intro k hk
    exact Finset.mem_singleton.mp hk ▸ Finset.mem_insert_self i {j}
  exact (Coordinate.RatioSubopens.coordinateRatioOn_change I V h
    (by rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair]; exact le_inf hi hj)
    i j (Finset.mem_singleton_self i)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
