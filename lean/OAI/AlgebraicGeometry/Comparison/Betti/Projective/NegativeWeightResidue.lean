import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.WeightInclusionFactors
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeMonomialResidue

/-! # Negative Weight Residue -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeWeightResidue.Dolbeault

noncomputable section

/-! The original comparison sends an original negative weight inclusion to its analytic coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveLaurentOriginalComparison_top_negative_weight (n k : ℕ) (j : Fin (n + 1))
    (e : NegativeLaurentMonomialExponents.Dolbeault.fullNegativeMonomialExponent (Fin (n + 1)) k)
    (s : SheafCohomology.Projective.OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of ℂ), ⊤)
      e.val.liftedNegativeSupport n) :
    ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue n j (-(k : ℤ))
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (-(k : ℤ))).f n
        (SheafCohomology.Projective.TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := ℂ) (-(k : ℤ)) e.val n s)) =
      NegativeAnalyticMonomial.Dolbeault.negativeAnalyticMonomial (n + 1) k e
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (s.val (NegativeMonomialResidue.Dolbeault.projectiveOrderedTopTuple n))) := by
  apply NegativeMonomialResidue.Dolbeault.projectiveLaurentOriginalComparison_top_negative_monomial
  exact Laurent.WeightInclusionFactors.Dolbeault.algebraicLaurentWeightInclusion_factor (R := ℂ) (-(k : ℤ)) e.val n
    (NegativeMonomialResidue.Dolbeault.projectiveOrderedTopTuple n) (NegativeMonomialResidue.Dolbeault.fullNegativeTopAllowedWeight n k e).property s

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeWeightResidue.Dolbeault
