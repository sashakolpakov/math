import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ConfigurationChartEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartOverlapEvaluation

/-! # Intersection Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.IntersectionMaps

noncomputable section

/-! Adding balanced exponent vectors gives the product denominator and
the canonical ring maps from each chart to their intersection chart. -/
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}
variable (i : Fin m) (a b : (Fin r → Fin m) → ℕ)
variable (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
variable (hb : b ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)

theorem balancedDeterminantMonomialElement_add :
    Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) =
      Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha * Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R b hb :=
  Subtype.ext (Balanced.MonomialAlgebra.exponentMonomial_add (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a b)

def balancedChartIntersectionLeft : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+*
    Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) :=
  HomogeneousLocalization.awayMap (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R b hb i)
    (balancedDeterminantMonomialElement_add R a b ha hb)

def balancedChartIntersectionRight : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i b hb →+*
    Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) :=
  HomogeneousLocalization.awayMap (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i)
    ((balancedDeterminantMonomialElement_add R a b ha hb).trans (mul_comm _ _))

variable {A : Type v} [CommRing A] [Algebra R A]

theorem balancedConfigurationChartEvaluation_intersection_left
    (w : Fin m → Fin r → A)
    (hwa : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a))
    (hwab : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) (a + b))) :
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) hwab).comp
        (balancedChartIntersectionLeft R i a b ha hb) =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hwa := by
  exact Homogeneous.ChartOverlapEvaluation.homogeneousAwayEvaluation_awayMap (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R b hb)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb))
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R b hb i)
    (balancedDeterminantMonomialElement_add R a b ha hb)
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) w).toRingHom
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) w a ha).symm ▸ hwa)
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) w (a + b)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb)).symm ▸ hwab)

theorem balancedConfigurationChartEvaluation_intersection_right
    (w : Fin m → Fin r → A)
    (hwb : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) b))
    (hwab : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) (a + b))) :
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) hwab).comp
        (balancedChartIntersectionRight R i a b ha hb) =
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w b hb hwb := by
  exact Homogeneous.ChartOverlapEvaluation.homogeneousAwayEvaluation_awayMap (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R b hb) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (a + b) ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb))
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i)
    ((balancedDeterminantMonomialElement_add R a b ha hb).trans (mul_comm _ _))
    (Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation (R := R) w).toRingHom
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) w b hb).symm ▸ hwb)
    ((Balanced.ConfigurationChartEvaluation.balancedConfigurationPolynomialEvaluation_denominator (R := R) w (a + b)
      ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb)).symm ▸ hwab)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.IntersectionMaps
