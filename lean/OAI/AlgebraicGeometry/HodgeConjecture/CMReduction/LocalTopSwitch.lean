import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopNamedIdentity
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalRegroupWithAmple
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedEliminate
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Connected

/-! # Local Top Switch -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopSwitch.CM.Construction

noncomputable section

section

open _root_.CategoryTheory
theorem localPairedTopEquation
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    BridgeRegroup.CM.Construction.bridgePairedTop E R₁ R₂ X
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
        (PackedMiddleTop.CM.Construction.packAmple R₁.abelianVariety.variety (R₁.abelianVariety.variety.complexDimension - 1)))
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
        (PackedMiddleTop.CM.Construction.packAmple R₂.abelianVariety.variety (R₂.abelianVariety.variety.complexDimension - 1))) =
    PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeMiddle R₁.abelianVariety R₂.abelianVariety X)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.abelianProduct R₁.abelianVariety R₂.abelianVariety).variety.toOver)
        (Albanese.Construction.SegreClosed.abelianProduct R₁.abelianVariety R₂.abelianVariety).variety.complexDimension
        (ProductTop.CM.Construction.productTopClass R₁.abelianVariety.variety R₂.abelianVariety.variety
          (MiddleTop.CM.Construction.middleTopClass E v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂))) := by
  with_reducible exact LocalTopNamedIdentity.CM.Construction.localPairedTopNamedIdentity E v₁ v₂ R₁ R₂ X

end

section

open _root_.CategoryTheory CartesianMonoidalCategory
abbrev localPairedTopFactorAlgebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver))
    (z₁ z₂ : X.variety.complexCohomology 1)
    (hprevious :
      PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
        (Bridge.CM.Construction.previousPacked E R₁ R₂ X U))
    (hswitch :
      PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
        (Bridge.CM.Construction.switchPacked E R₁ R₂ X z₁ z₂)) := by
  let W := Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X
  let F : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace W.variety.toOver) → Prop := fun t =>
    PackedRegroup.CM.Construction.IsAlgebraicEven W.variety
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X)
        (U * PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂) * t)
  have hall := LocalRegroupWithAmple.CM.Construction.localRegroupWithAmple h_LineBundleCycles h_ThomClass hlefschetz E v₁ v₂ R₁ R₂ X U z₁ z₂ hprevious hswitch
  have heq := localPairedTopEquation E v₁ v₂ R₁ R₂ X
  have hleft : F (BridgeRegroup.CM.Construction.bridgePairedTop E R₁ R₂ X
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
        (PackedMiddleTop.CM.Construction.packAmple R₁.abelianVariety.variety (R₁.abelianVariety.variety.complexDimension - 1)))
      (PackedRegroup.CM.Construction.evenPullback (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
        (PackedMiddleTop.CM.Construction.packAmple R₂.abelianVariety.variety (R₂.abelianVariety.variety.complexDimension - 1)))) := by
    with_reducible exact hall
  exact (congrArg F heq).mp hleft

end

/-! The geometric local contraction for a pair switch. Two old abelian
factors are integrated out after multiplying the previous endpoint class,
the four-factor switch class, and the actual ample powers. -/

open _root_.CategoryTheory CartesianMonoidalCategory

theorem local_switch_contraction
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver))
    (z₁ z₂ : X.variety.complexCohomology 1)
    (hprevious :
      PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
        (Bridge.CM.Construction.previousPacked E R₁ R₂ X U))
    (hswitch :
      PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
        (Bridge.CM.Construction.switchPacked E R₁ R₂ X z₁ z₂)) :
    PackedRegroup.CM.Construction.IsAlgebraicEven X.variety (U * PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂) := by
  let S : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := Albanese.Construction.SegreClosed.abelianProduct R₁.abelianVariety R₂.abelianVariety
  let b : S.variety.complexCohomology (S.variety.complexDimension + S.variety.complexDimension) := ProductTop.CM.Construction.productTopClass R₁.abelianVariety.variety R₂.abelianVariety.variety
    (MiddleTop.CM.Construction.middleTopClass E v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂)
  have hright := localPairedTopFactorAlgebraic h_LineBundleCycles h_ThomClass hlefschetz
    E v₁ v₂ R₁ R₂ X U z₁ z₂ hprevious hswitch
  have hb : b ≠ 0 := ProductTop.CM.Construction.productTopClass_ne_zero R₁.abelianVariety.variety R₂.abelianVariety.variety
    (MiddleTop.CM.Construction.middleTopClass E v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v₂ R₂)
    (MiddleTop.CM.Construction.middleTopClass_ne_zero E h_PolarizedPairing v₁ R₁) (PackedMiddleTop.CM.Construction.reverseMiddleTopClass_ne_zero E h_PolarizedPairing v₂ R₂)
  let : PathConnectedSpace S.variety.analyticSpace := Connected.CM.Construction.abelian_pathConnected S
  let : PathConnectedSpace X.variety.analyticSpace := Connected.CM.Construction.abelian_pathConnected X
  exact PackedEliminate.CM.Construction.packed_algebraic_of_top_factor h_Functoriality S.variety X.variety
    (U * PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂) b hb hright

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalTopSwitch.CM.Construction
