import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup

/-! # Bridge Regroup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeRegroup.CM.Construction

noncomputable section

/-! Named regrouped class on the actual bridge product. -/

open _root_.CategoryTheory

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
  (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

abbrev bridgePairedTop
    (L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ)
      (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver)) :=
  (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver)
    (Bridge.CM.Construction.bridgeVectorFirst E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (Bridge.CM.Construction.bridgeVectorFirst E R₁ R₂ X 1) * L₁) *
  (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver)
    (Bridge.CM.Construction.bridgeVectorSecond E R₁ R₂ X 1)
    (Bridge.CM.Construction.bridgeVectorSecond E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) * L₂)

theorem bridge_regroup_eq
    (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.variety.toOver))
    (L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ)
      (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver))
    (z₁ z₂ : X.variety.complexCohomology 1) :
    (Bridge.CM.Construction.previousPacked E R₁ R₂ X U * Bridge.CM.Construction.switchPacked E R₁ R₂ X z₁ z₂) * (L₁ * L₂) =
      PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X)
        (U * PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.variety.toOver) z₁ z₂) * bridgePairedTop E R₁ R₂ X L₁ L₂ := by
  have h := @PackedRegroup.CM.Construction.pullback_switch_regroup
    (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver X.variety.toOver (Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X) U L₁ L₂
    (Bridge.CM.Construction.bridgeVectorFirst E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (Bridge.CM.Construction.bridgeVectorSecond E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (Bridge.CM.Construction.bridgeVectorFirst E R₁ R₂ X 1) (Bridge.CM.Construction.bridgeVectorSecond E R₁ R₂ X 1) z₁ z₂
  convert h using 0
theorem bridge_regroup_algebraic (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.variety.toOver))
    (L₁ L₂ : EvenAlgebra.CM.Construction.EvenClass (R := ℂ)
      (Betti.Scheme.schemePointSpace (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver))
    (z₁ z₂ : X.variety.complexCohomology 1)
    (hprevious : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (Bridge.CM.Construction.previousPacked E R₁ R₂ X U))
    (hswitch : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (Bridge.CM.Construction.switchPacked E R₁ R₂ X z₁ z₂))
    (hL₁ : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety L₁)
    (hL₂ : PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety L₂) :
    PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X)
        (U * PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.variety.toOver) z₁ z₂) * bridgePairedTop E R₁ R₂ X L₁ L₂) := by
  let P := Bridge.CM.Construction.previousPacked E R₁ R₂ X U
  let Q := Bridge.CM.Construction.switchPacked E R₁ R₂ X z₁ z₂
  have hPQ := PackedRegroup.CM.Construction.IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass
    (V := (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety)
    (a := P) (b := Q) hprevious hswitch
  have hLL := PackedRegroup.CM.Construction.IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass
    (V := (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety)
    (a := L₁) (b := L₂) hL₁ hL₂
  have h := PackedRegroup.CM.Construction.IsAlgebraicEven.mul h_LineBundleCycles h_ThomClass
    (V := (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety)
    (a := P * Q) (b := L₁ * L₂) hPQ hLL
  have heq := bridge_regroup_eq E R₁ R₂ X U L₁ L₂ z₁ z₂
  rw [heq] at h
  convert h using 0

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeRegroup.CM.Construction
