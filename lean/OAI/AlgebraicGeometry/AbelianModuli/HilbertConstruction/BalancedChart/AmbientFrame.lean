import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartCrossMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.MonomialFractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialExponentExtension

/-! # Ambient Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientFrame

noncomputable section

/-! In the ambient localization the balanced coordinates are the
normalized point coordinates. The frame and chosen coordinates are units. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}

abbrev balancedChartAmbientRing (a : (Fin r → Fin m) → ℕ) :=
  Localization.Away (Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a)

def balancedChartAmbientVectors (a : (Fin r → Fin m) → ℕ) :
    Fin m → Fin r → balancedChartAmbientRing R a :=
  fun i j => algebraMap (MvPolynomial (Fin m × Fin r) R) (balancedChartAmbientRing R a)
    (MvPolynomial.X (i, j))

theorem balancedChartAmbientVectors_monomial (a b : (Fin r → Fin m) → ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (balancedChartAmbientVectors R a)) b =
      algebraMap (MvPolynomial (Fin m × Fin r) R) (balancedChartAmbientRing R a)
        (Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) b) := by
  rw [MonomialExponentExtension.exponentMonomial_map]
  congr 1
  funext σ
  exact (LabeledDeterminantPolynomials.labeledDeterminant_map
    (algebraMap (MvPolynomial (Fin m × Fin r) R) (balancedChartAmbientRing R a))
    σ (fun i j => MvPolynomial.X (i, j))).symm

theorem balancedChartAmbientVectors_denominator_isUnit (a : (Fin r → Fin m) → ℕ) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun σ => LabeledDeterminantPolynomials.labeledDeterminant σ (balancedChartAmbientVectors R a)) a) := by
  rw [balancedChartAmbientVectors_monomial]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem balancedChartAmbientVectors_frame_isUnit (σ : Fin r → Fin m) (e : Fin m)
    (a : (Fin r → Fin m) → ℕ) (h : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun (balancedChartAmbientRing R a) (Fin r))
      (fun j => balancedChartAmbientVectors R a (σ j)) (balancedChartAmbientVectors R a e)) := by
  rw [← Frame.ChartDenominators.frameDiscriminantExponent_monomial]
  exact Unit.MonomialFractions.exponentMonomial_isUnit_of_le _ h (balancedChartAmbientVectors_denominator_isUnit R a)

theorem balancedChartAmbientVectors_coordinate_isUnit (σ : Fin r → Fin m) (e z : Fin m) (c : Fin r)
    (a : (Fin r → Fin m) → ℕ) (h : Frame.CoordinateExponents.frameCoordinateExponent σ e z c ≤ a) :
    IsUnit (DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (balancedChartAmbientRing R a) (Fin r))
      (fun j => balancedChartAmbientVectors R a (σ j)) (balancedChartAmbientVectors R a e)
      (balancedChartAmbientVectors R a z) c) := by
  rw [← Frame.CoordinateMonomials.frameCoordinateExponent_linearMap]
  exact Unit.MonomialFractions.exponentMonomial_isUnit_of_le _ h (balancedChartAmbientVectors_denominator_isUnit R a)

theorem balancedFrameChartCoordinate_ambient_crossMultiply
    (i : Fin m) (σ : Fin r → Fin m) (e z : Fin m) (c k : Fin r)
    (a C : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) :
    (show balancedChartAmbientRing R a from
      Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m)
        (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
        (Balanced.FrameChartCoordinates.balancedFrameChartCoordinate R i σ e z c k a C ha hC)) *
        Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (balancedChartAmbientVectors R a))
          (Frame.CoordinateExponents.frameCoordinateExponent σ e z c) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (balancedChartAmbientVectors R a))
        (Frame.CoordinateExponents.frameCoordinateExponent σ e z k) := by
  rw [balancedChartAmbientVectors_monomial, balancedChartAmbientVectors_monomial]
  exact Homogeneous.ChartCrossMultiplication.homogeneousSubalgebraChartEmbedding_crossMultiply (Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m)
    (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i) (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i)
    (Balanced.FrameCoordinatePolynomials.balancedFrameCoordinateNumerator R σ e z c k a C ha hC)
    (Balanced.FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_mem_grading R σ e z c k a C ha hC i) _ _
    (Balanced.FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_crossMultiply R σ e z c k a C ha hC)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientFrame
