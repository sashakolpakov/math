import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectiveOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.IntersectionMaps

/-! # Balanced Chart Intersections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable

noncomputable section

/-! Intersections of stable balanced charts are themselves stable
balanced charts, using the sum of their exponent vectors. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {r m : ℕ}

def BalancedFrameIndex.StableBalancedFrameIndex.intersection (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    BalancedFrameIndex.StableBalancedFrameIndex.{u} r m where
  rank_two := j.rank_two
  points_two := j.points_two
  frame := j.frame
  additional := j.additional
  coordinate := j.coordinate
  exponent := j.exponent + k.exponent
  complement z := j.complement z + k.exponent
  balanced := (Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced
  frame_le := j.frame_le.trans (fun τ => Nat.le_add_right _ _)
  complete z := by
    calc
      j.complement z + k.exponent + Frame.CoordinateExponents.frameCoordinateExponent j.frame j.additional z (j.coordinate z) =
          (j.complement z + Frame.CoordinateExponents.frameCoordinateExponent j.frame j.additional z (j.coordinate z)) + k.exponent := by ac_rfl
      _ = _ := by rw [j.complete z]
  sparse := by
    intro K hK w hw
    rw [Balanced.MonomialAlgebra.exponentMonomial_add] at hw
    exact j.sparse K w (left_ne_zero_of_mul hw)

theorem BalancedChartIntersections.stableBalancedFrameOpen_intersection (R : Type u) [CommRing R] (i : Fin m)
    (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    BalancedProjectiveOpen.stableBalancedFrameOpen R i (j.intersection k) =
      BalancedProjectiveOpen.stableBalancedFrameOpen R i j ⊓ BalancedProjectiveOpen.stableBalancedFrameOpen R i k := by
  change Proj.basicOpen (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
      (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R (j.exponent + k.exponent)
        ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced)) = _
  rw [BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add, Proj.basicOpen_mul] <;> rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable
