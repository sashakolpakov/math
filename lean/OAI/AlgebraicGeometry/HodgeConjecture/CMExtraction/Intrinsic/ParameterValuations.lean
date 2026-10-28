import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SatakeParameters

/-! # Parameter Valuations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterValuations

noncomputable section

section

/-! Apply the full GaloisValuation to the constructed full Hecke triples themselves.
Their Galois compatibility is proved from the actual rational minuscule
operators. Only the initial identification with the radial projective
parameter remains an explicit parameter-identification premise. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation.Central

theorem native_full_projective_conjugate
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar) (β : Fin 3 → ParameterChoices.Qbar)
    (hβ : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ) β)
    (σ : Gal(ParameterChoices.Qbar/ℚ)) :
    RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
      (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
      (fun i => σ (β i)) := by
  obtain ⟨π, hπ⟩ := ParameterConjugation.nativeFullParameterTriple_conjugate D ParameterChoices.Qbar A χ σ
  obtain ⟨c, hc, τ, hτ⟩ := hβ
  refine ⟨σ c, (map_ne_zero σ).mpr hc, π.trans τ, ?_⟩
  intro i
  rw [hπ i, hτ (π i), map_mul]
  rfl

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hμ : D.reference.μ = E.val.toRingHom)
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

include hg hμ hv in
theorem native_full_parameter_valuations
    (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.reference,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (j : ParameterChoices.Qbar →+* ℂ) (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (a : ParameterChoices.Qbarˣ) (ha : (a : ParameterChoices.Qbar) ^ M = ω)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hprojective : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)⁻¹))) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      let P := MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
      (∃ z : ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) ∧
      ∀ z : ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
          (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  let ι := ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
  let P := fun σ : Gal(ParameterChoices.Qbar/ℚ) => MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
    (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
  have hP (σ : Gal(ParameterChoices.Qbar/ℚ)) : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ)
      (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)⁻¹) i)) :=
    native_full_projective_conjugate D A χ _ hprojective σ
  have hunit : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ((a : ParameterChoices.Qbar)⁻¹))‖ = 1 := by
    intro σ
    rw [map_inv₀, map_inv₀, norm_inv,
      Parameters.ParameterChoices.root_all_conjugates_norm_one j ω (a : ParameterChoices.Qbar) M hM ha hω σ, inv_one]
  have h := SatakeParameters.verifiedGaloisValuation E ιE (ParameterChoices.restriction E ιE) (ParameterChoices.restriction_commutes E ιE) v hv
    (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl) (Representatives.Multiplicity.nativeRepresentatives E D.reference)
    (Representatives.Multiplicity.nativeRepresentatives_active E D.reference hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E D.reference hg.reference_admissible hμ)
    q (Fact.out : q.Prime) M hM r hr (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q ι)
    (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_add q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_q q ι) hsplit
    (a : ParameterChoices.Qbar) (a : ParameterChoices.Qbar)⁻¹ ω ζ (-1) (Or.inr rfl) hζ
    (by simpa only [neg_one_mul] using hrel) ha (Or.inr rfl) j.toRatAlgHom hunit
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) P hP
  have hbase := (RootValuations.native_inverse_root_valuation E D hg hμ ιE v hv r M hM hsplit ω ζ hζ hrel a ha).1
  intro σ
  refine ⟨(h.2 σ).2.1, ?_⟩
  intro z hz
  have hzv := ((h.2 σ).2.2 z hz).2
  simpa only [inv_inv, ι, hbase] using hzv

include hg hμ hv in
theorem native_full_direct_root_parameter_valuations
    (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.Multiplicity.nativeRepresentatives E D.reference,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (j : ParameterChoices.Qbar →+* ℂ) (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (a : ParameterChoices.Qbarˣ) (ha : (a : ParameterChoices.Qbar) ^ M = ω)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hprojective : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)))) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      let P := MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
      (∃ z : ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) ∧
      ∀ z : ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
          (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2) := by
  let ι := ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
  let P := fun σ : Gal(ParameterChoices.Qbar/ℚ) => MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
    (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
  have hP (σ : Gal(ParameterChoices.Qbar/ℚ)) : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ)
      (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) ((a : ParameterChoices.Qbar)) i)) :=
    native_full_projective_conjugate D A χ _ hprojective σ
  have hunit : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (a : ParameterChoices.Qbar))‖ = 1 :=
    Parameters.ParameterChoices.root_all_conjugates_norm_one j ω (a : ParameterChoices.Qbar) M hM ha hω
  have h := SatakeParameters.verifiedGaloisValuation E ιE (ParameterChoices.restriction E ιE) (ParameterChoices.restriction_commutes E ιE) v hv
    (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl) (Representatives.Multiplicity.nativeRepresentatives E D.reference)
    (Representatives.Multiplicity.nativeRepresentatives_active E D.reference hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E D.reference hg.reference_admissible hμ)
    q (Fact.out : q.Prime) M hM r hr (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q ι)
    (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_add q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_q q ι) hsplit
    (a : ParameterChoices.Qbar) (a : ParameterChoices.Qbar) ω ζ (-1) (Or.inr rfl) hζ
    (by simpa only [neg_one_mul] using hrel) ha (Or.inl rfl) j.toRatAlgHom hunit
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) P hP
  have hbase : NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι (a : ParameterChoices.Qbar) = (3 / 2 : ℚ) := by
    simpa [hv, ComplexMultiplication.SignSwitch.CM.signValue] using
      RootValuations.native_dilation_root_conjugate_valuation E D hg hμ ιE v r M hM hsplit ω ζ hζ hrel a ha 1
  intro σ
  refine ⟨(h.2 σ).2.1, ?_⟩
  intro z hz
  have hzv := ((h.2 σ).2.2 z hz).2
  simpa only [inv_inv, ι, hbase] using hzv

end

/-! Every normalized parameter of a conjugated native full character is
the same conjugated radial root up to sign. Thus its norm bounds persist. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation.Central

theorem native_normalized_conjugate_root
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbar)
    (hnorm : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ a)‖ = 1)
    (hproj : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) a))
    (σ : Gal(ParameterChoices.Qbar/ℚ)) (z : ParameterChoices.Qbar)
    (hz : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
      (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) :
    (z = σ a ∨ z = -(σ a)) ∧ (∀ γ : Gal(ParameterChoices.Qbar/ℚ), ‖j (γ z)‖ = 1) := by
  have hp := RepresentationTheory.Hecke.GaloisValuationCm.projective_trans (RepresentationTheory.Hecke.GaloisValuationCm.projective_symm hz)
    (native_full_projective_conjugate D A χ _ hproj σ)
  rw [RepresentationTheory.Hecke.GaloisValuationCm.conjugate_triple] at hp
  have hs : (σ (DualRadialSatake.Iwasawa.algebraicSqrt q j)) ^ 2 = (q : ParameterChoices.Qbar) := by
    rw [← map_pow, DualRadialSatake.Iwasawa.algebraicSqrt_sq, map_natCast]
  have he := RepresentationTheory.Hecke.GaloisValuationCm.projective_parameter_unique q (Fact.out : q.Prime)
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) (σ (DualRadialSatake.Iwasawa.algebraicSqrt q j)) (σ a) z
    (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) hs j.toRatAlgHom (hnorm σ) hp
  refine ⟨he, ?_⟩
  intro γ
  rcases he with he | he
  · rw [he]
    exact hnorm (γ * σ)
  · rw [he, map_neg, map_neg, norm_neg]
    exact hnorm (γ * σ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterValuations
