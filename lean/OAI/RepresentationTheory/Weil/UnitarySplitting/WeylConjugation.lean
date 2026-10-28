import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients

/-! # Weyl Conjugation -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeylConjugation.Construction

noncomputable section

/-! Simultaneous Weyl translation of the two test vectors modulates the
matrix coefficient by the symplectic character. -/

open _root_.MeasureTheory

theorem weylMatrixCoefficient_conjugation
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
        (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f).val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w h).val v =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w) *
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val v := by
  let β := StandardTransvections.Construction.standardSymplecticBilinear F d
  have hAlt : ∀ x, β x x = 0 := StandardTransvections.Construction.standardSymplecticBilinear_alternating d
  have hb : Oscillator.Construction.standardSymplecticPairing d (-w) (v + w) = Oscillator.Construction.standardSymplecticPairing d v w := by
    change β (-w) (v + w) = β v w
    rw [map_neg, LinearMap.neg_apply, map_add, hAlt, add_zero,
      CayleyCompositionPhase.Construction.alternating_pairing_swap β hAlt w v, neg_neg]
  have hv : -w + (v + w) = v := by abel
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_input_shift hF ψ hc hu,
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift hF ψ hc hu, hb, hv,
    ← mul_assoc, ← ψ.map_add_eq_mul, add_halves]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeylConjugation.Construction
