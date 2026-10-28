import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.IntersectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEvaluation

/-! # Intersection Algebra Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps

noncomputable section

/-! Product-denominator restriction maps preserve the original
coefficient algebra. Their actual ring maps therefore define algebra
maps on both sides of every balanced chart intersection. -/
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def homogeneousAwayRestrictionAlgHom (g : ℕ → Submodule R S) [GradedAlgebra g]
    {f h x : S} {d : ℕ} (hh : h ∈ g d) (hx : x = f * h) :
    HomogeneousLocalization.Away g f →ₐ[R] HomogeneousLocalization.Away g x where
  __ := HomogeneousLocalization.awayMap g hh hx
  commutes' r := by
    rw [HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap,
      RingHom.comp_apply, RingHom.comp_apply]
    exact HomogeneousLocalization.awayMap_fromZeroRingHom g hh hx _

variable (R) {r m : ℕ} (i : Fin m) (a b : (Fin r → Fin m) → ℕ)
variable (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
variable (hb : b ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)

def balancedChartIntersectionLeftAlg : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R]
    FrameChartCoordinates.balancedDeterminantChartRing R i (a + b) ((ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) :=
  homogeneousAwayRestrictionAlgHom (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R b hb i)
    (BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add R a b ha hb)

def balancedChartIntersectionRightAlg : FrameChartCoordinates.balancedDeterminantChartRing R i b hb →ₐ[R]
    FrameChartCoordinates.balancedDeterminantChartRing R i (a + b) ((ExponentFiniteGeneration.balancedExponentMonoid _).add_mem ha hb) :=
  homogeneousAwayRestrictionAlgHom (DeterminantGrading.balancedDeterminantGrading R r m i)
    (FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i)
    ((BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add R a b ha hb).trans (mul_comm _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.IntersectionAlgebraMaps
