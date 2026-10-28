import OAI.AlgebraicGeometry.Albanese.Definitions
import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs

/-! # Hodge Comparison H -/

namespace OAI.AlgebraicGeometry.Albanese.HodgeComparisonH.CM

noncomputable section

/-! The HodgeComparison statement, with its proof supplied by the completed development. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- HodgeComparison: Albanese pullback is an isomorphism of rational Hodge structures. -/
theorem albanese_h1_hodge_iso
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver)
    (ha : Definitions.CM.HodgeComparison.IsAlbaneseMap X x₀ A a) :
    ∃ (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
      (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
      (e : A.variety.rationalCohomology 1 ≃ₗ[ℚ]
        X.rationalCohomology 1),
      Definitions.CM.HodgeComparison.IsCanonicalH1 A.variety HA ∧
      Definitions.CM.HodgeComparison.IsCanonicalH1 X HX ∧
      e.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HX e.toLinearMap ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HX HA e.symm.toLinearMap := by
  exact HodgeComparisonIs.CM.Construction.albanese_h1_hodge_iso X x₀ A a ha

end

end OAI.AlgebraicGeometry.Albanese.HodgeComparisonH.CM
