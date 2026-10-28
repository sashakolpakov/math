import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.LaurentEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurentMonomialEvaluation

/-! # Monomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Monomial.Dolbeault

noncomputable section

/-! The original analytification Cech map sends each algebraic Laurent monomial to that same homogeneous monomial. -/

open scoped BigOperators

open _root_.MvPolynomial

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistCechConeValue_original_map_monomial (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t))
    (e : SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent t)) (c : ℂ)
    (hz : LaurentEvaluation.Dolbeault.projectiveAlgebraicTwistCechLaurentCoordinates n j d q z t = AddMonoidAlgebra.single e c) :
    CechConeEvaluation.Dolbeault.projectiveTwistCechConeValue n j d q ((ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q z) t x =
      c * ∏ i, x.val i ^ (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv t d e).val.val i := by
  have hi : x.val (t 0) ≠ 0 :=
    (Laurent.SectorTo.Dolbeault.mem_laurentCoordinateDomain _ x.val).mp x.property (t 0)
      (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hp : (∏ i : {i : Fin (n + 1) // i ≠ t 0},
      Projective.CechLaurentPoints.Dolbeault.projectiveCechChartCoordinates n q (fun k => ULift.up (t k)) (LaurentEvaluation.Dolbeault.projectiveCechConePoint n q t x) i ^ e.val i) =
      ∏ i : {i : Fin (n + 1) // i ≠ t 0}, (x.val i.val / x.val (t 0)) ^ e.val i := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun v : ℂ => v ^ e.val i) (LaurentEvaluation.Dolbeault.projectiveCechConePoint_coordinates n q t x i)
  rw [LaurentEvaluation.Dolbeault.projectiveTwistCechConeValue_original_map_laurent, hz, Laurent.MonomialEvaluation.Dolbeault.allowedLaurentEvaluation_single, hp]
  calc
    x.val (t 0) ^ d * (c * ∏ i : {i : Fin (n + 1) // i ≠ t 0}, (x.val i.val / x.val (t 0)) ^ e.val i) =
      c * (x.val (t 0) ^ d * ∏ i : {i : Fin (n + 1) // i ≠ t 0}, (x.val i.val / x.val (t 0)) ^ e.val i) := by ring
    _ = _ := congrArg (c * ·) (HomogeneousLaurentMonomialEvaluation.Dolbeault.coordinateLaurentMonomial_homogeneous t d e x.val hi)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Monomial.Dolbeault
