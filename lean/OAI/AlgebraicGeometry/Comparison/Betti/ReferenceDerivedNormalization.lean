import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueDerived
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Hypercohomology

/-! # Reference Derived Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReferenceDerivedNormalization

noncomputable section

/-! The normalized direct-image cohomology map is literally BettiComparison's preserved algebraic-to-holomorphic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem algebraicToHolomorphicCohomologyMap_eq_directImage (n : ℕ) (x : Algebraic.Sheaves.algebraicDeRham X n) :
    Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n x =
      FlasqueDerived.directImageCohomologyMap (Analytification.Base.analytificationMap X)
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) (Holomorphic.Int.analyticHolomorphicSheafComplexInt X)
        (Holomorphic.Int.algebraicToHolomorphicDirectImageInt X) (n : ℤ) x := by
  let c := (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).map
    (Analytic.De.analytificationInverseImageConstantIso X).inv
  let s := (Analytic.De.analytificationInverseImage X).mapDerivedCategorySingleFunctor 0 |>.inv.app (Algebraic.Sheaves.constantComplexSheaf X)
  let p := (Analytic.De.derivedAnalytificationInverseImage X).map x
  let q := ((Analytic.De.derivedAnalytificationInverseImage X).commShiftIso (n : ℤ)).hom.app
    (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X))
  let r := (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
    (Holomorphic.Hypercohomology.derivedAlgebraicToHolomorphicForms X)
  change (c ≫ s) ≫ p ≫ q ≫ r = c ≫ s ≫ (p ≫ q) ≫ r
  exact (Category.assoc c s (p ≫ q ≫ r)).trans
    (congrArg (fun t => c ≫ s ≫ t) (Category.assoc p q r).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReferenceDerivedNormalization
