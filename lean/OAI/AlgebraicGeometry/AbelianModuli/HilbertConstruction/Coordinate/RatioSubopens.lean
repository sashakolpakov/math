import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

/-! # Ratio Subopens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSubopens

noncomputable section

/-! Coordinate ratios on arbitrary subopens, independent of enlarging the list of inverted coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateRatioOn (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (s : Finset (Fin (n + 1)))
    (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) (i j : Fin (n + 1)) (hi : i ∈ s) :
    Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), V) :=
  (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hV).op (RatioSections.coordinateRatioSection I s i j hi)

theorem coordinateRatioOn_self (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (s : Finset (Fin (n + 1)))
    (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) (i : Fin (n + 1)) (hi : i ∈ s) :
    coordinateRatioOn I V s hV i i hi = 1 := by
  unfold coordinateRatioOn
  rw [RatioSections.coordinateRatioSection_self]
  exact ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hV).op).hom.map_one

theorem coordinateRatioOn_comp (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (s : Finset (Fin (n + 1)))
    (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s) (i j k : Fin (n + 1)) (hi : i ∈ s) (hj : j ∈ s) :
    coordinateRatioOn I V s hV i j hi * coordinateRatioOn I V s hV j k hj =
      coordinateRatioOn I V s hV i k hi := by
  exact (((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hV).op).hom.map_mul _ _).symm.trans
    (congrArg ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hV).op)
      (RatioSections.coordinateRatioSection_comp I s i j k hi hj))

theorem coordinateRatioOn_change (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    {s t : Finset (Fin (n + 1))} (h : s ⊆ t) (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I t)
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    coordinateRatioOn I V s (hV.trans (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h)) i j hi =
      coordinateRatioOn I V t hV i j (h hi) := by
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (ProjectiveChart.RestrictionCoordinates.coordinateProjectiveChartOpen_antitone I h) hV
    (RatioSections.coordinateRatioSection I s i j hi)).symm.trans
      (congrArg ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hV).op)
        (RatioSections.coordinateRatioSection_restriction I h i j hi))

theorem coordinateRatioOn_restrict (V W : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens) (h : W ≤ V)
    (s : Finset (Fin (n + 1))) (hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s)
    (i j : Fin (n + 1)) (hi : i ∈ s) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE h).op (coordinateRatioOn I V s hV i j hi) =
      coordinateRatioOn I W s (h.trans hV) i j hi :=
  Relative.OpenFunctionUnits.openFunction_restriction_comp hV h (RatioSections.coordinateRatioSection I s i j hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RatioSubopens
