import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TwoSlots
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeSwitch
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ChangedEndpoint
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Paths

/-! # Endpoint Path -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EndpointPath.CM.Construction

noncomputable section

section

/-! Propagate endpoint algebraicity across one four-factor switch. -/

open _root_.CategoryTheory

theorem endpointAlgebraicity_distinct_step
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hrealization : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (p : ℕ) (v w z : Fin p → Pairing.CM.Construction.SignType E)
    (a b : Fin p) (hab : a ≠ b)
    (hrest : ∀ i, i ≠ a → i ≠ b → z i = w i)
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((w a).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((w b).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((z a).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((z b).val τ))
    (hprevious : Endpoints.CM.Construction.EndpointAlgebraicity E p v w) : Endpoints.CM.Construction.EndpointAlgebraicity E p v z := by
  cases p with
  | zero => exact Fin.elim0 a
  | succ r =>
    intro R T X s g
    obtain ⟨R₁⟩ := hrealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w a))
      ⟨ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization E (w a)⟩
    obtain ⟨R₂⟩ := hrealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w b))
      ⟨ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization E (w b)⟩
    let W : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := Bridge.CM.Construction.bridgeProduct R₁.abelianVariety R₂.abelianVariety X
    let f : W.toOver ⟶ X.toOver := Bridge.CM.Construction.bridgeBase R₁.abelianVariety R₂.abelianVariety X
    let f₁ : W.toOver ⟶ R₁.abelianVariety.toOver := Bridge.CM.Construction.bridgeFirst R₁.abelianVariety R₂.abelianVariety X
    let f₂ : W.toOver ⟶ R₂.abelianVariety.toOver := Bridge.CM.Construction.bridgeSecond R₁.abelianVariety R₂.abelianVariety X
    let D := Endpoints.CM.Construction.changedData E w z a b hrest T R₁ R₂ W X f g f₁ f₂
    let t : Fin (r + 1) → X.variety.complexCohomology 1 :=
      fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (s i) (Endpoints.CM.Construction.realizedVector E (R i) 1)
    have hp := hprevious R (fun i => (D i).1) W (fun i => f ≫ s i) (fun i => (D i).2)
    rw [ChangedEndpoint.CM.Construction.endpointClass_changed E v w z a b hrest R T R₁ R₂ W X f s g f₁ f₂] at hp
    have hs := BridgeSwitch.CM.Construction.switchPacked_algebraic h_LineBundleCycles E hswitch (w a) (w b) (z a) (z b)
      hbalance R₁ R₂ (T a) (T b) X (g a) (g b)
    have hslots : Fin.natAdd (r + 1) a ≠ Fin.natAdd (r + 1) b := by
      intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    exact TwoSlots.CM.Construction.two_slot_contraction h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing hlefschetz hexterior E
      (w a) (w b) R₁ R₂ X r (Fin.natAdd (r + 1) a) (Fin.natAdd (r + 1) b) hslots
      (ChangedEndpoint.CM.Construction.changedTuple E w z a b hrest T R₁ R₂ W X f g f₁ f₂ t) (ChangedEndpoint.CM.Construction.targetTuple E z T X g t)
      (ChangedEndpoint.CM.Construction.changedTuple_rest E w z a b hrest T R₁ R₂ W X f g f₁ f₂ t)
      (ChangedEndpoint.CM.Construction.changedTuple_first E w z a b hrest T R₁ R₂ W X f g f₁ f₂ t)
      (ChangedEndpoint.CM.Construction.changedTuple_second E w z a b hrest T R₁ R₂ W X f g f₁ f₂ t hab) hp (by
        simpa only [ChangedEndpoint.CM.Construction.targetTuple, Fin.append_right] using hs)

theorem endpointAlgebraicity_step
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hrealization : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (p : ℕ) (v w z : Fin p → Pairing.CM.Construction.SignType E)
    (hstep : ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch w z) (hprevious : Endpoints.CM.Construction.EndpointAlgebraicity E p v w) :
    Endpoints.CM.Construction.EndpointAlgebraicity E p v z := by
  rcases Paths.CM.Construction.oddSwitch_eq_or_distinct hstep with heq | ⟨a, b, hab, hrest, hbalance⟩
  · subst z
    exact hprevious
  · exact endpointAlgebraicity_distinct_step h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing hlefschetz hexterior
      E hrealization hswitch p v w z a b hab hrest hbalance hprevious

end

/-! Induction through the finite chain of odd four-factor switches. -/

theorem endpointAlgebraicity_chain
    (h_ScalarDescent : Descent.CM.Construction.ScalarDescentInput)
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hrealization : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (p : ℕ) (v w : Fin p → Pairing.CM.Construction.SignType E) (hchain : ComplexMultiplication.OddSignSwitch.CM.OddSwitchChain v w) :
    Endpoints.CM.Construction.EndpointAlgebraicity E p v w := by
  induction hchain with
  | refl => exact Endpoints.CM.Construction.endpointAlgebraicity_refl E h_ScalarDescent hlefschetz hexterior h_LineBundleCycles h_ThomClass p v
  | @tail w z _ hstep ih =>
    exact endpointAlgebraicity_step h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing hlefschetz hexterior
      E hrealization hswitch p v w z hstep ih

theorem endpointAlgebraicity_of_PairSwitches
    (h_ScalarDescent : Descent.CM.Construction.ScalarDescentInput) (h_PairSwitches : Paths.CM.Construction.PairSwitchesInput)
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hrealization : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hswitch : Definitions.CM.FourFactorSwitchAlgebraicity E)
    (p : ℕ) (v w : Fin p → Pairing.CM.Construction.SignType E)
    (hbalance : ∀ τ : Gal(E/ℚ),
      (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val τ)) = ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val τ)) :
    Endpoints.CM.Construction.EndpointAlgebraicity E p v w := by
  obtain ⟨n, path, hv, hw, hstep, _⟩ := h_PairSwitches E p v w hbalance
  have hc := Paths.CM.Construction.chain_of_indexed_path ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch n path hstep
  rw [hv, hw] at hc
  exact endpointAlgebraicity_chain h_ScalarDescent h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing hlefschetz hexterior
    E hrealization hswitch p v w hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EndpointPath.CM.Construction
