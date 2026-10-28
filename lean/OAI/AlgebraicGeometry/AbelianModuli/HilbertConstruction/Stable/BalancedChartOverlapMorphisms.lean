import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedAffineCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartIntersections

/-! # Balanced Chart Overlap Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartOverlapMorphisms

noncomputable section

/-! The two maps from a product-denominator chart agree with its
inclusion in the stable quotient open, so the affine chart constructions
are compatible as actual scheme morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m)

private theorem chart_map_ext {C : Type*} [Category C] {V X Y Z : C}
    (f : V ⟶ X) (a : X ⟶ Y) (b : V ⟶ Y) (m : Y ⟶ Z) [Mono m]
    (a' : X ⟶ Z) (b' : V ⟶ Z) (ha : a ≫ m = a') (hb : b ≫ m = b')
    (h : f ≫ a' = b') : f ≫ a = b := by
  apply (cancel_mono m).mp
  rw [Category.assoc, ha, hb]
  exact h

theorem stableBalancedAffineChartMap_intersection_left :
    Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionLeft R i j.exponent k.exponent j.balanced k.balanced)) ≫
        BalancedAffineCover.stableBalancedAffineChartMap R i j = BalancedAffineCover.stableBalancedAffineChartMap R i (j.intersection k) := by
  refine chart_map_ext _ _ _ (BalancedProjectiveOpen.stableBalancedProjectiveOpen R (r := r) i).ι _ _
    (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i j)
    (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i (j.intersection k)) ?_
  exact Proj.SpecMap_awayMap_awayι (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R j.exponent j.balanced i) (j.degree_positive i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R k.exponent k.balanced i)
    (BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add R j.exponent k.exponent j.balanced k.balanced)

theorem stableBalancedAffineChartMap_intersection_right :
    Spec.map (CommRingCat.ofHom (BalancedChart.IntersectionMaps.balancedChartIntersectionRight R i j.exponent k.exponent j.balanced k.balanced)) ≫
        BalancedAffineCover.stableBalancedAffineChartMap R i k = BalancedAffineCover.stableBalancedAffineChartMap R i (j.intersection k) := by
  refine chart_map_ext _ _ _ (BalancedProjectiveOpen.stableBalancedProjectiveOpen R (r := r) i).ι _ _
    (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i k)
    (BalancedAffineCover.stableBalancedAffineChartMap_comp_inclusion R i (j.intersection k)) ?_
  exact Proj.SpecMap_awayMap_awayι (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R k.exponent k.balanced i) (k.degree_positive i)
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R j.exponent j.balanced i)
    ((BalancedChart.IntersectionMaps.balancedDeterminantMonomialElement_add R j.exponent k.exponent j.balanced k.balanced).trans (mul_comm _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedChartOverlapMorphisms
