import OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.TopHomologyCycles
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeTopCoefficients

/-! # Negative Homology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeHomology.Dolbeault

noncomputable section

/-! The original comparison on top cohomology has the canonical negative coefficient formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveLaurentOriginalComparison_top_negative_homology (q k : ℕ) (j : Fin (q + 2))
    (s : SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles (R := ℂ) (σ := Fin (q + 2)) (-(k : ℤ)) (q + 1)) :
    (ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j (-(k : ℤ))).hom
      (HomologicalComplex.homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (q + 1) j (-(k : ℤ))) (q + 1)
        ((PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesHomologyIso q j (-(k : ℤ))).hom s)) =
      Algebraic.AnalyticNegativeCoefficients.Dolbeault.algebraicNegativeLaurentCoefficientEquiv (q + 2) k
        (NegativeTopCoefficients.Dolbeault.projectiveFullNegativeTopCoefficients (q + 1) k s.val) := by
  let B := LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (q + 1) j (-(k : ℤ))
  let E := ProjectiveTwist.TopCohomology.Dolbeault.projectiveTwistTopCechHomologyIso q j (-(k : ℤ))
  let z := PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesLift (q + 1) j (-(k : ℤ)) s
  have h₀ := ConcreteCategory.congr_hom
    (PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesHomologyIso_hom q j (-(k : ℤ))) s
  have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality B (q + 1)) z
  have h₂ := TopHomologyCycles.Dolbeault.projectiveTwistTopCechHomologyIso_homologyπ q j (-(k : ℤ))
    (HomologicalComplex.cyclesMap B (q + 1) z)
  have h₃ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i B (q + 1)) z
  have h₄ := ConcreteCategory.congr_hom
    (PositiveVanishing.Dolbeault.projectiveLaurentNegativeCyclesLift_i (q + 1) j (-(k : ℤ))) s
  exact (congrArg (fun y => E.hom (HomologicalComplex.homologyMap B (q + 1) y)) h₀).trans
    ((congrArg E.hom h₁).trans (h₂.trans
      ((congrArg (ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j (-(k : ℤ))) h₃).trans
        ((congrArg (fun x => ProjectiveTwist.TopResidue.Dolbeault.projectiveTwistTopResidue (q + 1) j (-(k : ℤ)) (B.f (q + 1) x)) h₄).trans
          (NegativeTopCoefficients.Dolbeault.projectiveLaurentOriginalComparison_top_negative_assembly (q + 1) k j s.val)))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativeHomology.Dolbeault
