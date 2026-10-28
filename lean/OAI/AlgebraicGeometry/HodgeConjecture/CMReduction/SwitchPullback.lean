import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Switch
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization

/-! # Switch Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SwitchPullback.CM.Construction

noncomputable section

/-! A four-factor switch class pulls back along any four algebraic maps,
using the actual product supplied by the switch hypothesis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem fourFactorSwitch_algebraic_pullback
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) 4
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i)
        ((R i).complexComparison
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) ∈
      X.complexGeometricAlgebraicClasses 2 := by
  obtain ⟨B, π, ⟨hprod⟩, hB⟩ := hswitch v hbalance R
  let δ : X.toOver ⟶ B.toOver := hprod.lift (Fan.mk X.toOver f)
  have hδ (i : Fin 4) : δ ≫ π i = f i := hprod.fac (Fan.mk X.toOver f) ⟨i⟩
  let x : Fin 4 → B.variety.complexCohomology 1 := fun i =>
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
      ((R i).complexComparison
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
          (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))
  have hx : IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace B.toOver) 4 x ∈
      B.variety.complexGeometricAlgebraicClasses 2 := by
    rw [CupAppend.CM.Construction.h1Cup_four]
    exact hB
  have hp := ComplexOperations.CM.Construction.complex_pullback_algebraic h_LineBundleCycles (X := X) (Y := B.variety) δ 2 _ hx
  rw [CupAppend.CM.Construction.scheme_h1Cup_pullback] at hp
  have heq (i : Fin 4) : Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 δ (x i) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i)
        ((R i).complexComparison
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))) := by
    change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 δ
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i) _) = _
    rw [CupPullback.CM.Construction.scheme_pullback_comp, hδ]
  simpa only [heq] using hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SwitchPullback.CM.Construction
