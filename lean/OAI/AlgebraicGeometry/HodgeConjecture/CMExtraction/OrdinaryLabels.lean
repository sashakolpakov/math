import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryActiveCharacter

/-! # Ordinary Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryLabels.Intrinsic

noncomputable section

/-! Fix all ordinary coefficient labels from the retained archimedean
list. The opposite comparison place gives exactly the original local
characters in every block, including the active rank-one block. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryActiveCharacter.ParameterChoices

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom)

def retainedOrdinaryLabels : (Fin s × Bool) ≃ Gal(E/ℚ) :=
  (Equiv.ofBijective (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ))
    (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ).complete).trans (Equiv.mulLeft (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

theorem retainedOrdinaryLabels_active :
    retainedOrdinaryLabels E P hP hμ (P.distinguished, false) = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P P.distinguished = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
  rw [Multiplicity.Period.nativeArchLabel_active E P hμ, mul_one]

theorem retainedOrdinaryLabels_conjugate (w : Fin s) (b : Bool) :
    retainedOrdinaryLabels E P hP hμ (w, !b) =
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * retainedOrdinaryLabels E P hP hμ (w, b) := by
  have hc : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E = 1 := by
    apply AlgEquiv.ext
    intro x
    exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E x
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) (w, !b) =
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) (w, b))
  cases b <;> simp [HeckeCycles.PairedCompletion.CM.placeIndex, ← mul_assoc, hc]

theorem retainedOrdinaryLabels_character
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j₀ j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
    (hj : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp iota =
      ((HeckeCycles.QadicModelMap.CM.localFieldEmbedding j₀).comp iota).comp (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E).toRingHom)
    (w : Fin s × Bool) :
    j.localCharacter iota (retainedOrdinaryLabels E P hP hμ w) =
      HeckeCycles.PairedCompletion.CM.pairedCharacter E j₀ iota (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w := by
  ext a
  apply Subtype.ext
  have hleft := RingHom.congr_fun j.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom
      (iota.comp (retainedOrdinaryLabels E P hP hμ w).toRingHom) a)
  have hright := RingHom.congr_fun j₀.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom
      (iota.comp (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w).toRingHom) a)
  change (j.localCharacter iota (retainedOrdinaryLabels E P hP hμ w) a : ℚ_[q]) =
    HeckeCycles.QadicModelMap.CM.localFieldEmbedding j (iota (retainedOrdinaryLabels E P hP hμ w (a : E))) at hleft
  change (HeckeCycles.PairedCompletion.CM.pairedCharacter E j₀ iota (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w a : ℚ_[q]) =
    HeckeCycles.QadicModelMap.CM.localFieldEmbedding j₀ (iota (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w (a : E))) at hright
  refine hleft.trans ((RingHom.congr_fun hj _).trans ?_)
  change HeckeCycles.QadicModelMap.CM.localFieldEmbedding j₀ (iota
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w (a : E))))) = _
  rw [ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]
  exact hright.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryLabels.Intrinsic
