import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Family
import OAI.RepresentationTheory.Hecke.GaloisValuationCm

/-! # Root Valuations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RootValuations

noncomputable section

/-! The same native dilation identity determines the valuation of every
dilation root and every Galois conjugate. The inverse root in the actual
inverse-transpose Satake triple has valuation exactly -3/2. -/

open scoped Classical

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hμ : D.reference.μ = E.val.toRingHom)
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

include hg hμ in
theorem native_dilation_root_conjugate_valuation (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.reference,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (a : ParameterChoices.Qbarˣ) (ha : (a : ParameterChoices.Qbar) ^ M = ω) (σ : Gal(ParameterChoices.Qbar/ℚ)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
      (σ (a : ParameterChoices.Qbar)) = (3 / 2 : ℚ) * ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) := by
  have h := RepresentationTheory.Hecke.GaloisValuationCm.dilation_root_valuation ιE (ParameterChoices.restriction E ιE) (ParameterChoices.restriction_commutes E ιE)
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_ne_one E) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E)
    (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (RepresentationTheory.Hecke.GaloisValuationCm.inverse_sign_odd E v _ (fun _ => rfl))
    (Representatives.Multiplicity.nativeRepresentatives E D.reference)
    (Representatives.Multiplicity.nativeRepresentatives_paired E D.reference hg.reference_admissible hμ)
    r M hM (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)))
    (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) hsplit (a : ParameterChoices.Qbar) ω ζ a.ne_zero (-1) hζ
    (by simpa only [neg_one_mul] using hrel) ha σ
  simpa only [Int.cast_neg, Int.cast_one, neg_neg, one_mul, inv_inv] using h

include hg hμ hv in
theorem native_inverse_root_valuation (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.reference,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (a : ParameterChoices.Qbarˣ) (ha : (a : ParameterChoices.Qbar) ^ M = ω) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
      ((a : ParameterChoices.Qbar)⁻¹) = (-3 / 2 : ℚ) ∧
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ ((a : ParameterChoices.Qbar)⁻¹)) =
        (-3 / 2 : ℚ) * ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) := by
  have hc (σ : Gal(ParameterChoices.Qbar/ℚ)) : NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ ((a : ParameterChoices.Qbar)⁻¹)) =
        (-3 / 2 : ℚ) * ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) := by
    rw [map_inv₀, RepresentationTheory.Hecke.GaloisValuationCm.val_inv _ (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) _ ((map_ne_zero σ).mpr a.ne_zero),
      native_dilation_root_conjugate_valuation E D hg hμ ιE v r M hM hsplit ω ζ hζ hrel a ha σ]
    ring
  refine ⟨?_, hc⟩
  simpa [hv, ComplexMultiplication.SignSwitch.CM.signValue] using hc 1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RootValuations
