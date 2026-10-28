import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeConjugateNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RootValuations

/-! # Satake Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SatakeParameters

noncomputable section

/-! Full GaloisValuation applied to the actual algebraic Satake character. The
normalized conjugate parameters are constructed from its rational
transform; every projectively equivalent normalized parameter has the
native valuation sign. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeConjugateNormalization.Iwasawa
open scoped Classical

theorem verifiedGaloisValuation : NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.GaloisValuationInput := RepresentationTheory.Hecke.GaloisValuationCm.galois_sign_rule_for_parameter_valuations

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hμ : D.reference.μ = E.val.toRingHom)
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

include hg hμ hv in
theorem native_actual_satake_parameters (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.reference,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (j : ParameterChoices.Qbar →+* ℂ) (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (a : ParameterChoices.Qbarˣ) (ha : (a : ParameterChoices.Qbar) ^ M = ω) :
    ∃ p : Gal(ParameterChoices.Qbar/ℚ) → ParameterChoices.Qbarˣ,
      (∀ σ, σ.toAlgHom.comp (DualRadialSatake.Iwasawa.algebraicDualSatakeCharacter q j a) =
        SatakeBaseChange.Iwasawa.torusSatakeOver q (SatakeConjugateNormalization.Iwasawa.normalizedTorusPoint (DualRadialSatake.Iwasawa.algebraicSqrtUnit q j) (p σ))) ∧
      (∀ σ, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) (p σ : ParameterChoices.Qbar))
        (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)⁻¹) i))) ∧
      (∀ (σ : Gal(ParameterChoices.Qbar/ℚ)) (z : ParameterChoices.Qbar),
        RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) (p σ : ParameterChoices.Qbar))
          (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
          (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2)) := by
  choose p _ hp hprojective using SatakeConjugateNormalization.Iwasawa.algebraicDualSatakeCharacter_normalized_conjugate q j a
  have hP (σ : Gal(ParameterChoices.Qbar/ℚ)) : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) (p σ : ParameterChoices.Qbar))
      (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)⁻¹) i)) :=
    RepresentationTheory.Hecke.GaloisValuationCm.projective_symm (hprojective σ)
  have hunit : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ((a : ParameterChoices.Qbar)⁻¹))‖ = 1 := by
    intro σ
    rw [map_inv₀, map_inv₀, norm_inv,
      Parameters.ParameterChoices.root_all_conjugates_norm_one j ω (a : ParameterChoices.Qbar) M hM ha hω σ, inv_one]
  have hsigns := NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.signs_of_full_GaloisValuation verifiedGaloisValuation E ιE (ParameterChoices.restriction E ιE) (ParameterChoices.restriction_commutes E ιE)
    v hv (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl)
    (Representatives.Multiplicity.nativeRepresentatives E D.reference) (Representatives.Multiplicity.nativeRepresentatives_active E D.reference hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E D.reference hg.reference_admissible hμ)
    q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) M hM r hr hsplit
    (a : ParameterChoices.Qbar) (a : ParameterChoices.Qbar)⁻¹ ω ζ (-1) (Or.inr rfl) hζ
    (by simpa only [neg_one_mul] using hrel) ha (Or.inr rfl) j.toRatAlgHom hunit
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j)
    (fun σ => RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) (p σ : ParameterChoices.Qbar)) hP
  have hbase := (RootValuations.native_inverse_root_valuation E D hg hμ ιE v hv r M hM hsplit ω ζ hζ hrel a ha).1
  refine ⟨p, hp, hP, ?_⟩
  intro σ z hz
  exact (hsigns.2 σ z hz).trans (congrArg (fun b : ℚ =>
    (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * b) hbase)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SatakeParameters
