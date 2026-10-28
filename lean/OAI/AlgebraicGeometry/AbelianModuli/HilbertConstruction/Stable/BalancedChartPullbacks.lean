import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartOverlapMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # Balanced Chart Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartPullbacks

noncomputable section

/-! The product-denominator affine chart is the actual scheme-theoretic
intersection of two stable affine charts over the stable quotient open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] {r m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m)

theorem stableBalancedChartIntersection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionLeft R i j.exponent k.exponent j.balanced k.balanced)))
      (Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionRight R i j.exponent k.exponent j.balanced k.balanced)))
      (BalancedAffineCover.stableBalancedAffineChartMap R i j) (BalancedAffineCover.stableBalancedAffineChartMap R i k) := by
  let g := Balanced.DeterminantGrading.balancedDeterminantGrading R r m i
  let f := Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R j.exponent j.balanced
  let h := Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R k.exponent k.balanced
  let hf := Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R j.exponent j.balanced i
  let hh := Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R k.exponent k.balanced i
  let he := BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add R j.exponent k.exponent j.balanced k.balanced
  let L := Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionLeft R i j.exponent k.exponent j.balanced k.balanced))
  let M := Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionRight R i j.exponent k.exponent j.balanced k.balanced))
  have Hraw : IsPullback L M (Proj.awayι g f hf (j.degree_positive i))
      (Proj.awayι g h hh (k.degree_positive i)) := by
    let E := Proj.pullbackAwayιIso g hf (j.degree_positive i) hh (k.degree_positive i) he
    refine IsPullback.of_iso_pullback ⟨?_⟩ E.symm ?_ ?_
    · exact (Proj.SpecMap_awayMap_awayι g hf (j.degree_positive i) hh he).trans
        (Proj.SpecMap_awayMap_awayι g hh (k.degree_positive i) hf (he.trans (mul_comm _ _))).symm
    · exact Proj.pullbackAwayιIso_inv_fst g hf (j.degree_positive i) hh (k.degree_positive i) he
    · exact Proj.pullbackAwayιIso_inv_snd g hf (j.degree_positive i) hh (k.degree_positive i) he
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors _ _ (BalancedProjectiveOpen.stableBalancedProjectiveOpen R (r := r) i).ι
      (BalancedAffineCover.stableBalancedAffineChartMap R i j) (BalancedAffineCover.stableBalancedAffineChartMap R i k)
      (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i j)
      (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i k) Hraw.cone Hraw.isLimit)

def stableBalancedChartPullbackIso :
    pullback (BalancedAffineCover.stableBalancedAffineChartMap R i j) (BalancedAffineCover.stableBalancedAffineChartMap R i k) ≅
      Spec (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i (j.exponent + k.exponent)
        ((Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).add_mem j.balanced k.balanced))) :=
  (stableBalancedChartIntersection_isPullback R i j k).isoPullback.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartPullbacks
