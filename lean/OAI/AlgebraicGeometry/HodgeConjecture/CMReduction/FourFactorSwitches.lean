import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.EndpointPath
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MonomialTransfer

/-! # Four Factor Switches -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.FourFactorSwitches.CM.Construction

noncomputable section

/-!
# CMReduction: four-factor switches imply the CM Hodge claim

The conclusion and the geometric background hypotheses are those of
Statements/CMReduction.lean. The additional named inputs are the actual prerequisite
propositions ScalarDescent, PairSwitches, Functoriality, LineBundleCycles, ThomClass and the weight-one clause of PolarizedPairing.
No statement stub is used as a proof. All intermediate endpoint tensors,
polarization contractions, product pushforwards, monomial transfers and
rational descent are proved in the imported CMReduction helpers.
-/

open scoped BigOperators Classical

theorem four_factor_switches_imply_cm
    (h_ScalarDescent : Descent.CM.Construction.ScalarDescentInput) (h_PairSwitches : Paths.CM.Construction.PairSwitchesInput)
    (h_Functoriality : CycleOperations.CM.Construction.FunctorialityInput) (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput) (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput)
    (hrealization :
      ∀ (E : IntermediateField ℚ ℂ)
        [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
        ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization E)
    (hfullness : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (hcycles : ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge)
    (hswitch :
      ∀ (E : IntermediateField ℚ ℂ)
        [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E],
        Definitions.CM.FourFactorSwitchAlgebraicity E) : ComplexMultiplication.CMCore.CM.cmHodgeClaim := by
  intro A hA p _
  obtain ⟨H, hhol, hanti, ⟨D⟩⟩ := hA
  obtain ⟨C⟩ := hexterior A H hhol hanti
  apply le_antisymm (hcycles A.variety p)
  intro a ha
  apply C.rational_hodge_mem_geometric_of_monomials D p ?_ a ha
  intro s hs
  apply MonomialTransfer.CM.Construction.monomial_algebraic_of_endpoint D C hhol hanti
    (hrealization D.commonCoefficientField) hfullness p s
  apply EndpointPath.CM.Construction.endpointAlgebraicity_of_PairSwitches h_ScalarDescent h_PairSwitches h_Functoriality h_LineBundleCycles h_ThomClass h_PolarizedPairing
    hlefschetz hexterior D.commonCoefficientField
    (hrealization D.commonCoefficientField) (hswitch D.commonCoefficientField) p
  intro τ
  have hsum := (D.exteriorEmbeddingTuple_signSum (p + p) s τ).trans (hs τ)
  rw [Fin.sum_univ_add] at hsum
  simp only [ComplexMultiplication.OddSignSwitch.CM.OddSignPattern.neg_apply, ComplexMultiplication.SignSwitch.CM.signValue_not, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hsum

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.FourFactorSwitches.CM.Construction
