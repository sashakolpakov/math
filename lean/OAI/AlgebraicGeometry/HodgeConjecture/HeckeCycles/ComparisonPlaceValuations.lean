import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ClosureEmbeddingTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

/-! # Comparison Place Valuations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPlaceValuations.CM

noncomputable section

/-! Transfer source parameter valuations to any original comparison
embedding with the conjugate coefficient-field restriction. The actual
algebraic roots and full Hecke character are retained. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters.ParameterChoices OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
  {q : ℕ} [Fact q.Prime]

theorem roots (ι₁ ι₂ : CMExtraction.ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q])
    (hE : ∀ x : E, ι₂ (ιE x) = ι₁ (ιE (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x))) (a : CMExtraction.ParameterChoices.Qbar)
    (hroot : ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι₁ (σ a) =
      (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2))
    (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι₂ (σ a) = (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  let τ := ClosureEmbeddingTransport.CM.transport ι₁ ι₂
  have hτ : CMExtraction.ParameterChoices.restriction E ιE τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E :=
    ClosureEmbeddingTransport.CM.restriction_eq E ιE ι₁ ι₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) hE
  have h := hroot (τ * σ)
  rw [map_mul, hτ, v.property] at h
  have he : NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι₂ (σ a) = NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι₁ (τ (σ a)) :=
    congrArg (NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q) (ClosureEmbeddingTransport.CM.compatibility ι₁ ι₂ (σ a)).symm
  exact he.trans (h.trans (by cases v.val (CMExtraction.ParameterChoices.restriction E ιE σ) <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue]))

variable {K : Type} [Field K] [NumberField K] {s : ℕ}
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
  (χ : CMExtraction.ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[CMExtraction.ParameterChoices.Qbar] CMExtraction.ParameterChoices.Qbar)
  (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (a : CMExtraction.ParameterChoices.Qbar)

theorem normalized
    (hnorm : ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ a)‖ = 1)
    (hproj : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) a))
    (hval : ∀ (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) (z : CMExtraction.ParameterChoices.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A
        (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2))
    (ι : CMExtraction.ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q])
    (hE : ∀ x : E, ι (ιE x) =
      CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false) (ιE (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)))
    (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) (z : CMExtraction.ParameterChoices.Qbar)
    (hz : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D CMExtraction.ParameterChoices.Qbar A
      (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q ι z = (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  have hr := CMExtraction.Intrinsic.OppositeParameters.native_root_values_of_normalized_values E D A χ j a ιE v hnorm hproj hval
  have hv := roots E ιE v _ ι hE a hr σ
  have hn : σ a ≠ 0 := by
    intro he
    have h := hnorm σ
    simp [he] at h
  rcases (CMExtraction.Intrinsic.ParameterValuations.native_normalized_conjugate_root D A χ j a hnorm hproj σ z hz).1 with he | he
  · exact he.symm ▸ hv
  · rw [he, RepresentationTheory.Hecke.GaloisValuationCm.val_neg _ (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) _ hn]
    exact hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPlaceValuations.CM
