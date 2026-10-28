import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Labels

noncomputable section

/-! IsogenyQuotient's two-summand labels use the exact ordered conjugate pairs of
the retained TateComparison model. No new ordering or representatives are chosen. -/

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM

def kernelPairEquiv (s : ℕ) : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Fin s × Bool where
  toFun := Sum.elim (fun v => (v, false)) (fun v => (v, true))
  invFun p := if p.2 then Sum.inr p.1 else Sum.inl p.1
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨v, b⟩; cases b <;> rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom)

def retainedIsogenyQuotientLabels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ) :=
  (kernelPairEquiv s).trans
    (Equiv.ofBijective (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ))
      (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ).complete)

theorem retainedIsogenyQuotientLabels_chosen (v : Fin s) :
    retainedIsogenyQuotientLabels E P hP hμ (Sum.inl v) = Multiplicity.Period.nativeArchLabel E P v := rfl

theorem retainedIsogenyQuotientLabels_opposite (v : Fin s) :
    retainedIsogenyQuotientLabels E P hP hμ (Sum.inr v) =
      ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P v := rfl

theorem retainedIsogenyQuotientLabels_swap (v : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s) :
    retainedIsogenyQuotientLabels E P hP hμ (Sum.swap v) =
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * retainedIsogenyQuotientLabels E P hP hμ v := by
  have hc : PELModuli.CMPoints.Arithmetic.rationalConjugation E = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
    apply AlgEquiv.ext
    intro x
    rfl
  rw [hc]
  cases v with
  | inl v => rfl
  | inr v =>
      rw [show Sum.swap (Sum.inr v) = Sum.inl v from rfl,
        retainedIsogenyQuotientLabels_chosen, retainedIsogenyQuotientLabels_opposite, ← mul_assoc]
      have hcc : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E = 1 := by
        apply AlgEquiv.ext
        exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E
      rw [hcc, one_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Labels
