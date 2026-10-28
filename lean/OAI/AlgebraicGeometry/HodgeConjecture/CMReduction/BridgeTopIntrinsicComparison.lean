import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTop
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeRegroup

/-! # Bridge Top Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIntrinsicComparison.CM.Construction

noncomputable section

open _root_.CategoryTheory

private theorem evenClass_snd_heq {X : TopCat.{0}} {a b : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) X}
    (h : a = b) : HEq a.2 b.2 := by
  cases h
  rfl

abbrev bridgePairedTopNativeComparison
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := by
  have hp := BridgeTop.CM.Construction.pullback_productTopClass R₁.abelianVariety.variety R₂.abelianVariety.variety
    (Bridge.CM.Construction.bridgeMiddle R₁.abelianVariety R₂.abelianVariety X)
    (MiddleTop.CM.Construction.middleTopClass E v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂)
  have hp' : PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeMiddle R₁.abelianVariety R₂.abelianVariety X)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.abelianProduct R₁.abelianVariety R₂.abelianVariety).variety.toOver)
        (Albanese.Construction.SegreClosed.abelianProduct R₁.abelianVariety R₂.abelianVariety).variety.complexDimension
        (ProductTop.CM.Construction.productTopClass R₁.abelianVariety.variety R₂.abelianVariety.variety
          (MiddleTop.CM.Construction.middleTopClass E v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂))) =
    PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R₁.abelianVariety.variety.toOver) R₁.abelianVariety.variety.complexDimension
        (MiddleTop.CM.Construction.middleTopClass E v₁ R₁)) *
    PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R₂.abelianVariety.variety.toOver) R₂.abelianVariety.variety.complexDimension
        (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂))  := by
    apply Sigma.ext (congrArg Sigma.fst hp)
    exact evenClass_snd_heq hp
  have h₁ := BridgeTop.CM.Construction.pullback_middleTopClass E v₁ R₁ (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
  have h₂ := BridgeTop.CM.Construction.pullback_reverseMiddleTopClass E v₂ R₂ (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
  have hprod := congrArg₂ (fun a b : EvenAlgebra.CM.Construction.EvenClass (R := ℂ)
    (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver) => a * b) h₁ h₂
  have hresult := (hp'.trans hprod).symm
  exact hresult

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIntrinsicComparison.CM.Construction
