import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation

/-! # Parameter Valuations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ParameterValuations.CM

noncomputable section

/-! Full GaloisValuation carries the original source root valuation to the same
full Hecke character's actual minuscule parameter triples. Rational
Galois conjugation of those operators supplies projective equivariance. -/

open scoped Classical TensorProduct BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation.Central
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

theorem full_projective_conjugate
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (χ : CMExtraction.ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[CMExtraction.ParameterChoices.Qbar] CMExtraction.ParameterChoices.Qbar) (β : Fin 3 → CMExtraction.ParameterChoices.Qbar)
    (hβ : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A χ) β)
    (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) :
    RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
      (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A
        (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
      (fun i => σ (β i)) := by
  obtain ⟨π, hπ⟩ := CMExtraction.Intrinsic.ParameterConjugation.nativeFullParameterTriple_conjugate D CMExtraction.ParameterChoices.Qbar A χ σ
  obtain ⟨c, hc, τ, hτ⟩ := hβ
  refine ⟨σ c, (map_ne_zero σ).mpr hc, π.trans τ, ?_⟩
  intro i
  rw [hπ i, hτ (π i), map_mul]
  rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (places : GeometricSource.CM.Places E)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)

include hv in
theorem valuations
    (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (ω ζ : CMExtraction.ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
      (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (hω : ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (a : CMExtraction.ParameterChoices.Qbarˣ) (ha : (a : CMExtraction.ParameterChoices.Qbar) ^ M = ω)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : CMExtraction.ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[CMExtraction.ParameterChoices.Qbar] CMExtraction.ParameterChoices.Qbar)
    (sqrt : CMExtraction.ParameterChoices.Qbar) (hsqrt : sqrt ^ 2 = (q : CMExtraction.ParameterChoices.Qbar))
    (hprojective : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple sqrt (a : CMExtraction.ParameterChoices.Qbar))) :
    ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ),
      let P := CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A
        (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
      (∃ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple sqrt z)) ∧
      ∀ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual P (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple sqrt z) →
        NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
          (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2) := by
  let ι := CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
  let P := fun σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ) => CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A
    (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
  have hP (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ)
      (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple sqrt (a : CMExtraction.ParameterChoices.Qbar) i)) :=
    full_projective_conjugate D A χ _ hprojective σ
  have hunit : ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ (a : CMExtraction.ParameterChoices.Qbar))‖ = 1 :=
    CMExtraction.Parameters.ParameterChoices.root_all_conjugates_norm_one j ω (a : CMExtraction.ParameterChoices.Qbar) M hM ha hω
  have h := RepresentationTheory.Hecke.GaloisValuationCm.galois_sign_rule_for_parameter_valuations E ιE (CMExtraction.ParameterChoices.restriction E ιE)
    (CMExtraction.ParameterChoices.restriction_commutes E ιE) v hv (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl)
    (Representatives.CM.representatives E places) (Representatives.CM.active E places) (Representatives.CM.paired E places)
    q (Fact.out : q.Prime) M hM r hr (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q ι)
    (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_add q ι) (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_q q ι) hsplit
    (a : CMExtraction.ParameterChoices.Qbar) (a : CMExtraction.ParameterChoices.Qbar) ω ζ (-1) (Or.inr rfl) hζ
    (by simpa only [neg_one_mul] using hrel) ha (Or.inl rfl) j.toRatAlgHom hunit
    sqrt hsqrt P hP
  have hbase := Auxiliary.CM.RootValuations.base_valuation E places D ιE v r M hM hsplit ω ζ hζ hrel a ha hv
  intro σ
  refine ⟨(h.2 σ).2.1, ?_⟩
  intro z hz
  have hzv := ((h.2 σ).2.2 z hz).2
  simpa only [inv_inv, ι, hbase] using hzv

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ParameterValuations.CM
