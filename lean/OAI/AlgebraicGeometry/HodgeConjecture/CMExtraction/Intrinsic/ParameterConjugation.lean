import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterUniqueness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters

/-! # Parameter Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation

noncomputable section

/-! Conjugate a full character through its rational algebra, and prove
that the constructed native triple changes only by conjugation and
permutation. No matching of independently chosen roots is assumed. -/

open scoped TensorProduct

namespace Central

variable {F H : Type*} [Field F] [Algebra ℚ F] [Ring H] [Algebra ℚ H]

def conjugateFullCharacter (χ : F ⊗[ℚ] H →ₐ[F] F) (σ : F ≃ₐ[ℚ] F) :
    F ⊗[ℚ] H →ₐ[F] F :=
  AlgHom.liftEquiv ℚ F H F (σ.toAlgHom.comp
    ((χ.restrictScalars ℚ).comp Algebra.TensorProduct.includeRight))

theorem conjugateFullCharacter_one_tmul (χ : F ⊗[ℚ] H →ₐ[F] F)
    (σ : F ≃ₐ[ℚ] F) (h : H) :
    conjugateFullCharacter χ σ (1 ⊗ₜ[ℚ] h) = σ (χ (1 ⊗ₜ[ℚ] h)) := by
  change (1 : F) * σ (χ (1 ⊗ₜ[ℚ] h)) = _
  exact one_mul _

theorem conjugateFullCharacter_inverse (χ : F ⊗[ℚ] H →ₐ[F] F) (σ : F ≃ₐ[ℚ] F) :
    conjugateFullCharacter (conjugateFullCharacter χ σ) σ.symm = χ := by
  apply (AlgHom.liftEquiv ℚ F H F).symm.injective
  apply AlgHom.ext
  intro h
  change conjugateFullCharacter (conjugateFullCharacter χ σ) σ.symm (1 ⊗ₜ[ℚ] h) =
    χ (1 ⊗ₜ[ℚ] h)
  rw [conjugateFullCharacter_one_tmul, conjugateFullCharacter_one_tmul, σ.symm_apply_apply]

end Central

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation.Central

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem nativeFullParameterTriple_conjugate
    (F : Type*) [Field F] [CharZero F] [Algebra ℚ F] [IsAlgClosed F]
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (σ : F ≃ₐ[ℚ] F) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i,
      MinusculeParameters.nativeFullParameterTriple D F A (Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) i =
        σ (MinusculeParameters.nativeFullParameterTriple D F A χ (π i)) := by
  obtain ⟨_, ht₁, ht₂, ht₃⟩ := MinusculeParameters.nativeFullParameterTriple_spec D F A χ
  obtain ⟨_, hc₁, hc₂, hc₃⟩ := MinusculeParameters.nativeFullParameterTriple_spec D F A (Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ)
  have hq : (q : F) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  apply ParameterUniqueness.Central.parameter_triple_unique
    (MinusculeParameters.nativeFullParameterTriple D F A (Central.conjugateFullCharacter (F := F) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ))
    (fun i => σ (MinusculeParameters.nativeFullParameterTriple D F A χ i))
  · apply mul_left_cancel₀ hq
    rw [← hc₁, Central.conjugateFullCharacter_one_tmul, ht₁]
    simp only [map_mul, map_natCast, map_add]
  · apply mul_left_cancel₀ hq
    rw [← hc₂, Central.conjugateFullCharacter_one_tmul, ht₂]
    simp only [map_mul, map_natCast, map_add]
  · rw [← hc₃, Central.conjugateFullCharacter_one_tmul, ht₃]
    simp only [map_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterConjugation
