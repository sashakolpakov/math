import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge

/-! # Bridge Vector Names -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeVectorNames.CM.Construction

noncomputable section

open _root_.CategoryTheory
variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
  (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (τ : Gal(E/ℚ))
theorem bridgeVectorFirst_def :
    Bridge.CM.Construction.bridgeVectorFirst E R₁ R₂ X τ =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
        (Endpoints.CM.Construction.realizedVector E R₁ τ) := rfl
theorem bridgeVectorSecond_def :
    Bridge.CM.Construction.bridgeVectorSecond E R₁ R₂ X τ =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
        (Endpoints.CM.Construction.realizedVector E R₂ τ) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeVectorNames.CM.Construction
