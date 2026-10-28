import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIntrinsicComparison

/-! # Bridge Top Identity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIdentity.CM.Construction

noncomputable section

open _root_.CategoryTheory

abbrev bridgePairedTop_eq
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  BridgeTopIntrinsicComparison.CM.Construction.bridgePairedTopNativeComparison E v₁ v₂ R₁ R₂ X

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIdentity.CM.Construction
