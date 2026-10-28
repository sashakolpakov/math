import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.SwitchPullback
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup

/-! # Bridge Switch -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeSwitch.CM.Construction

noncomputable section

/-! The four-factor hypothesis supplies precisely the switch class on
the bridge product used by the geometric contraction. -/

open _root_.CategoryTheory

theorem switchPacked_algebraic
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (v₁ v₂ w₁ w₂ : Pairing.CM.Construction.SignType E)
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue (v₁.val τ) + ComplexMultiplication.SignSwitch.CM.signValue (v₂.val τ) = ComplexMultiplication.SignSwitch.CM.signValue (w₁.val τ) + ComplexMultiplication.SignSwitch.CM.signValue (w₂.val τ))
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₁))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v₂))
    (T₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E w₁))
    (T₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E w₂))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (g₁ : X.toOver ⟶ T₁.abelianVariety.toOver)
    (g₂ : X.toOver ⟶ T₂.abelianVariety.toOver) :
    PackedRegroup.CM.Construction.IsAlgebraicEven (Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety
      (Bridge.CM.Construction.switchPacked E R₁ R₂ X
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g₁ (Endpoints.CM.Construction.realizedVector E T₁ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g₂ (Endpoints.CM.Construction.realizedVector E T₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))) := by
  let W : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X
  let f : W.toOver ⟶ X.toOver := Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X
  let f₁ : W.toOver ⟶ R₁.abelianVariety.toOver := Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X
  let f₂ : W.toOver ⟶ R₂.abelianVariety.toOver := Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X
  let v : Fin 4 → Pairing.CM.Construction.SignType E := ![v₁, v₂, w₁, w₂]
  let R : ∀ i : Fin 4, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) :=
    Fin.cases R₁ (Fin.cases R₂ (Fin.cases T₁ (Fin.cases T₂ (fun i => Fin.elim0 i))))
  let π : ∀ i : Fin 4, W.toOver ⟶ (R i).abelianVariety.toOver :=
    Fin.cases f₁ (Fin.cases f₂ (Fin.cases (f ≫ g₁) (Fin.cases (f ≫ g₂) (fun i => Fin.elim0 i))))
  have hv : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ) := hbalance
  have h := SwitchPullback.CM.Construction.fourFactorSwitch_algebraic_pullback h_LineBundleCycles E hswitch v hv R W.variety π
  let i₁ : W.variety.complexCohomology 1 := Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₁ (Endpoints.CM.Construction.realizedVector E R₁ 1)
  let i₂ : W.variety.complexCohomology 1 := Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₂ (Endpoints.CM.Construction.realizedVector E R₂ 1)
  let z₁ : X.variety.complexCohomology 1 := Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g₁ (Endpoints.CM.Construction.realizedVector E T₁ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
  let z₂ : X.variety.complexCohomology 1 := Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g₂ (Endpoints.CM.Construction.realizedVector E T₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
  have heq :
      (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
        ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
          (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
      ![i₁, i₂, Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f z₁, Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f z₂] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact (CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f g₁ 1
        (Endpoints.CM.Construction.realizedVector E T₁ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))).symm
    · exact (CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f g₂ 1
        (Endpoints.CM.Construction.realizedVector E T₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))).symm
  rw [heq] at h
  change PackedRegroup.CM.Construction.IsAlgebraicEven W.variety
    (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace W.toOver) i₁ i₂ * PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.toOver) z₁ z₂))
  rw [PackedRegroup.CM.Construction.evenPullback_pair, ← PackedRegroup.CM.Construction.packH1Cup_four]
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeSwitch.CM.Construction
