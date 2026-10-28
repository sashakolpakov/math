import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameCoordinatePolynomials
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-! # Frame Chart Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartCoordinates

noncomputable section

/-! The normalized point coordinates are elements of the actual affine
chart ring of Proj. The chosen coordinate of each point is exactly one. -/
open scoped BigOperators Classical
universe u
variable (R : Type u) [CommRing R] {r m : ℕ}

abbrev balancedDeterminantChartRing (i : Fin m) (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) :=
  HomogeneousLocalization.Away (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha)

def balancedFrameChartCoordinate (i : Fin m) (σ : Fin r → Fin m)
    (e z : Fin m) (c k : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) : balancedDeterminantChartRing R i a ha :=
  HomogeneousLocalization.Away.mk (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i) 1
    (FrameCoordinatePolynomials.balancedFrameCoordinateNumerator R σ e z c k a C ha hC)
    (by simpa only [one_nsmul] using FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_mem_grading R σ e z c k a C ha hC i)

theorem balancedFrameChartCoordinate_selected (i : Fin m) (σ : Fin r → Fin m)
    (e z : Fin m) (c : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) :
    balancedFrameChartCoordinate R i σ e z c c a C ha hC = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [balancedFrameChartCoordinate, HomogeneousLocalization.Away.val_mk,
    FrameCoordinatePolynomials.balancedFrameCoordinateNumerator_selected, HomogeneousLocalization.val_one, pow_one,
    Localization.mk_eq_mk', IsLocalization.mk'_self]

theorem balancedFrameChartCoordinate_span (i : Fin m) (σ : Fin r → Fin m)
    (e z : Fin m) (c : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) :
    Ideal.span (Set.range (fun k => balancedFrameChartCoordinate R i σ e z c k a C ha hC)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← balancedFrameChartCoordinate_selected R i σ e z c a C ha hC]
  exact Ideal.subset_span (Set.mem_range_self c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartCoordinates
