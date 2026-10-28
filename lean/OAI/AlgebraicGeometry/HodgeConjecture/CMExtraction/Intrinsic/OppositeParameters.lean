import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterValuations

/-! # Opposite Parameters -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters.ParameterChoices

/-! The ordinary Lie-rank-one block is the conjugate embedding. Choose
its comparison closure explicitly and retain the same algebraic roots. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)

def nativeOppositeGaloisLift : Gal(ParameterChoices.Qbar/ℚ) :=
  Classical.choose (ParameterChoices.restriction_surjective E ιE (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

theorem nativeOppositeGaloisLift_restriction :
    ParameterChoices.restriction E ιE (nativeOppositeGaloisLift E ιE) = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E :=
  Classical.choose_spec (ParameterChoices.restriction_surjective E ιE (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

variable {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeOppositeClosureEmbedding : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q] :=
  (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)).comp
    (nativeOppositeGaloisLift E ιE).toRingHom

theorem nativeOppositeClosureEmbedding_spec (hq : D.IsGoodCompletelySplitPrime) (x : E) :
    nativeOppositeClosureEmbedding E ιE D (ιE x) =
      algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])
        (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true) x) := by
  change ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
    (nativeOppositeGaloisLift E ιE (ιE x)) = _
  rw [ParameterChoices.restriction_commutes, nativeOppositeGaloisLift_restriction, ClosureSplitting.ParameterChoices.nativeClosureEmbedding_spec]
  congr 1
  exact (RingHom.congr_fun (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq D.reference.distinguished false) x).symm

variable (v : Multiplicity.Odd.Sign E)

theorem native_opposite_root_valuation (a : ParameterChoices.Qbar)
    (hroot : ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ a) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2))
    (σ : Gal(ParameterChoices.Qbar/ℚ)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (nativeOppositeClosureEmbedding E ιE D) (σ a) =
      (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  have h := hroot (nativeOppositeGaloisLift E ιE * σ)
  rw [map_mul, nativeOppositeGaloisLift_restriction, v.property] at h
  change NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
    (nativeOppositeGaloisLift E ιE (σ a)) = _
  exact h.trans (by cases v.val (ParameterChoices.restriction E ιE σ) <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue])

variable (hg : D.HasIntegralModelGeometry) (hμ : D.reference.μ = E.val.toRingHom)
  (j : ParameterChoices.Qbar →+* ℂ) (hι : ∀ x : E, j (ιE x) = (x : ℂ))
  {F : Type} [Field F] [NumberField F] [IsGalois ℚ F]
  (i : K →+* F) (f : F →+* ℚ_[q])

def nativeOppositeQadicChoice : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q :=
  CompatibleQadicChoice.ParameterChoices.normalExtensionQadicChoice D.complexEmbedding j (nativeOppositeClosureEmbedding E ιE D) i f

include hg hμ hι in
theorem nativeOppositeQadicChoice_local (hq : D.IsGoodCompletelySplitPrime) :
    (HeckeCycles.QadicModelMap.CM.localFieldEmbedding (nativeOppositeQadicChoice E ιE D j i f)).comp D.fieldEmbedding =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true) := by
  let J := nativeOppositeQadicChoice E ιE D j i f
  have hE := CompatibleQadicChoice.ParameterChoices.native_fieldInChosenClosure_restrict E D hg hμ j ιE hι
  ext x
  apply (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).injective
  have h := RingHom.congr_fun J.closure_compatibility (D.fieldEmbedding x)
  change nativeOppositeClosureEmbedding E ιE D
    (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure j D.complexEmbedding (D.fieldEmbedding x)) =
      algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J (D.fieldEmbedding x)) at h
  have hx : CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure j D.complexEmbedding (D.fieldEmbedding x) = ιE x :=
    RingHom.congr_fun hE x
  rw [hx, nativeOppositeClosureEmbedding_spec E ιE D hq] at h
  exact h.symm

theorem nativeOppositeQadicChoice_closures :
    (nativeOppositeQadicChoice E ιE D j i f).complexClosure = j ∧
    (nativeOppositeQadicChoice E ιE D j i f).iota = nativeOppositeClosureEmbedding E ιE D ∧
    (nativeOppositeQadicChoice E ιE D j i f).fieldInClosure =
      (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure j D.complexEmbedding).toRingHom := ⟨rfl, rfl, rfl⟩

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters.ParameterChoices

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

/-! Transfer the already derived native parameter valuations to the
conjugate comparison place required by the ordinary rank-one block. -/

open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
  (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
  (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbar) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E)
  (hnorm : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ a)‖ = 1)
  (hproj : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ)
    (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) a))

include hnorm hproj

theorem native_root_values_of_normalized_values
    (hval : ∀ (σ : Gal(ParameterChoices.Qbar/ℚ)) (z : ParameterChoices.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2)) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ a) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2) := by
  intro σ
  obtain ⟨z, hz⟩ := RepresentationTheory.Hecke.GaloisValuationCm.normalize_conjugate_triple q (DualRadialSatake.Iwasawa.algebraicSqrt q j) a
    (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) σ
  have hp := RepresentationTheory.Hecke.GaloisValuationCm.projective_trans (ParameterValuations.native_full_projective_conjugate D A χ _ hproj σ) hz
  have hv := hval σ z hp
  have hn : σ a ≠ 0 := by
    intro he
    have h := hnorm σ
    simp [he] at h
  rcases (ParameterValuations.native_normalized_conjugate_root D A χ j a hnorm hproj σ z hp).1 with he | he
  · exact he ▸ hv
  · rw [he, RepresentationTheory.Hecke.GaloisValuationCm.val_neg _ (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) _ hn] at hv
    exact hv

theorem native_opposite_normalized_values
    (hval : ∀ (σ : Gal(ParameterChoices.Qbar/ℚ)) (z : ParameterChoices.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2)) :
    ∀ (σ : Gal(ParameterChoices.Qbar/ℚ)) (z : ParameterChoices.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A
        (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (ParameterChoices.nativeOppositeClosureEmbedding E ιE D) z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  have hr := native_root_values_of_normalized_values E D A χ j a ιE v hnorm hproj hval
  intro σ z hz
  have hv := ParameterChoices.native_opposite_root_valuation E ιE D v a hr σ
  have hn : σ a ≠ 0 := by
    intro he
    have h := hnorm σ
    simp [he] at h
  rcases (ParameterValuations.native_normalized_conjugate_root D A χ j a hnorm hproj σ z hz).1 with he | he
  · exact he.symm ▸ hv
  · rw [he, RepresentationTheory.Hecke.GaloisValuationCm.val_neg _ (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) _ hn]
    exact hv

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

end

end OAI
