import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalRegroupWithAmple
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeVectorNames

/-! # Local Top Named Identity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopNamedIdentity

noncomputable section

open _root_.CategoryTheory CartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CM.Construction
private theorem evenClass_snd_comparison {X : TopCat.{0}} {a b : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X}
    (h : a = b) : HEq a.2 b.2 := by
  cases h
  rfl
abbrev localPairedTopNamedIdentity
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := by
  have h := BridgeTopIdentity.CM.Construction.bridgePairedTop_eq E v₁ v₂ R₁ R₂ X
  conv at h =>
    lhs; lhs; lhs; arg 2
    rw [← BridgeVectorNames.CM.Construction.bridgeVectorFirst_def E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)]
  conv at h =>
    lhs; lhs; lhs; arg 3
    rw [← BridgeVectorNames.CM.Construction.bridgeVectorFirst_def E R₁ R₂ X 1]
  conv at h =>
    lhs; rhs; lhs; arg 2
    rw [← BridgeVectorNames.CM.Construction.bridgeVectorSecond_def E R₁ R₂ X 1]
  conv at h =>
    lhs; rhs; lhs; arg 3
    rw [← BridgeVectorNames.CM.Construction.bridgeVectorSecond_def E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)]
  exact h

end CM.Construction

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopNamedIdentity
