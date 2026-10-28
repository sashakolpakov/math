import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTopIdentity
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedEliminate
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Connected

/-! # Local Regroup With Ample -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalRegroupWithAmple.CM.Construction

noncomputable section

/-! The geometric local contraction for a pair switch. Two old abelian
factors are integrated out after multiplying the previous endpoint class,
the four-factor switch class, and the actual ample powers. -/

open _root_.CategoryTheory CartesianMonoidalCategory

theorem amplePullback_algebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ Y.toOver) (d : ℕ) :
    PackedRegroup.CM.Construction.IsAlgebraicEven X (PackedRegroup.CM.Construction.evenPullback f (PackedMiddleTop.CM.Construction.packAmple Y d)) :=
  PackedRegroup.CM.Construction.IsAlgebraicEven.pullback h_LineBundleCycles (X := X) (Y := Y) f
    (PackedMiddleTop.CM.Construction.packAmple_algebraic hlefschetz h_LineBundleCycles h_ThomClass Y d)

abbrev bridgeAmpleFirstAlgebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  amplePullback_algebraic h_LineBundleCycles h_ThomClass hlefschetz
    (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety R₁.abelianVariety.variety
    (Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
    (R₁.abelianVariety.variety.complexDimension - 1)

abbrev bridgeAmpleSecondAlgebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v₁ v₂ : Pairing.CM.Construction.SignType E)
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  amplePullback_algebraic h_LineBundleCycles h_ThomClass hlefschetz
    (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety R₂.abelianVariety.variety
    (Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
    (R₂.abelianVariety.variety.complexDimension - 1)

abbrev localRegroupWithAmple
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
  let f₁ := Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X
  let f₂ := Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X
  let L₁ :=
    PackedRegroup.CM.Construction.evenPullback f₁ (PackedMiddleTop.CM.Construction.packAmple R₁.abelianVariety.variety (R₁.abelianVariety.variety.complexDimension - 1))
  let L₂ :=
    PackedRegroup.CM.Construction.evenPullback f₂ (PackedMiddleTop.CM.Construction.packAmple R₂.abelianVariety.variety (R₂.abelianVariety.variety.complexDimension - 1))
  have hL₁ := bridgeAmpleFirstAlgebraic h_LineBundleCycles h_ThomClass hlefschetz E v₁ v₂ R₁ R₂ X
  have hL₂ := bridgeAmpleSecondAlgebraic h_LineBundleCycles h_ThomClass hlefschetz E v₁ v₂ R₁ R₂ X
  have hall := BridgeRegroup.CM.Construction.bridge_regroup_algebraic E R₁ R₂ X h_LineBundleCycles h_ThomClass U L₁ L₂ z₁ z₂ hprevious hswitch hL₁ hL₂
  exact hall

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LocalRegroupWithAmple.CM.Construction
