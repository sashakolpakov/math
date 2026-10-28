import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.FrameCoordinateValues

/-! # Frame Chart Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization

noncomputable section

/-! The actual coordinates in a balanced Proj chart normalize the
selected frame to the standard projective frame. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}
variable (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
variable (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
variable (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
variable (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)

def balancedFrameChartVectors : Fin m → Fin r → FrameChartCoordinates.balancedDeterminantChartRing R i a ha :=
  fun z k => FrameChartCoordinates.balancedFrameChartCoordinate R i σ e z (c z) k a (C z) ha (hC z)

theorem balancedFrameChartVectors_selected (z : Fin m) :
    balancedFrameChartVectors R i σ e c a C ha hC z (c z) = 1 :=
  FrameChartCoordinates.balancedFrameChartCoordinate_selected R i σ e z (c z) a (C z) ha (hC z)

theorem balancedFrameChartVectors_normalizes
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    (∀ k, balancedFrameChartVectors R i σ e c a C ha hC e k = 1) ∧
      ∀ j k, balancedFrameChartVectors R i σ e c a C ha hC (σ j) k = if j = k then 1 else 0 := by
  let E : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* BalancedChart.AmbientFrame.balancedChartAmbientRing R a :=
    Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
    (DeterminantGrading.balancedDeterminantGrading R r m i) (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
  let v := BalancedChart.AmbientFrame.balancedChartAmbientVectors R a
  let b := fun j => v (σ j)
  let T := DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) (Fin r)) b (v e)
  have hΔ := BalancedChart.AmbientFrame.balancedChartAmbientVectors_frame_isUnit R σ e a hframe
  have hx (z : Fin m) (k : Fin r) :
      E (balancedFrameChartVectors R i σ e c a C ha hC z k) * T (v z) (c z) = T (v z) k := by
    have h := BalancedChart.AmbientFrame.balancedFrameChartCoordinate_ambient_crossMultiply R i σ e z (c z) k a (C z) ha (hC z)
    simp only [Frame.CoordinateMonomials.frameCoordinateExponent_linearMap] at h
    exact h
  have he := Normalized.FrameCoordinateValues.normalizedDeterminantFrame_additional
    (Pi.basisFun (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) (Fin r)) b (v e) hΔ (c e)
    (fun k => E (balancedFrameChartVectors R i σ e c a C ha hC e k)) (hx e)
  have hb (j : Fin r) := Normalized.FrameCoordinateValues.normalizedDeterminantFrame_basis
    (Pi.basisFun (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) (Fin r)) b (v e) hΔ j (c (σ j))
    (fun k => E (balancedFrameChartVectors R i σ e c a C ha hC (σ j) k)) (hx (σ j))
  constructor
  · intro k
    apply Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_injective (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
      (DeterminantGrading.balancedDeterminantGrading R r m i) (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    exact (congrFun he k).trans (map_one E).symm
  · intro j k
    apply Homogeneous.SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_injective (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
      (DeterminantGrading.balancedDeterminantGrading R r m i) (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)
    change E (balancedFrameChartVectors R i σ e c a C ha hC (σ j) k) = E (if j = k then 1 else 0)
    by_cases hjk : j = k <;> simpa [hjk] using congrFun (hb j) k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization
