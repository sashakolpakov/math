import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCharacters

/-! # Projective Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveUniqueness

noncomputable section

/-! The actual chosen full native triples are projectively independent
of the full character extension of the same active SL3 character. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCharacters.Local

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (F : Type*) [Field F] [CharZero F] [Algebra ℚ F] [IsAlgClosed F]

def nativeGL3RationalCharacter (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ] F :=
  ((Minuscule.Intrinsic.nativeGL3Character D F χ).restrictScalars ℚ).comp Algebra.TensorProduct.includeRight

theorem native_full_triples_projectively_equal (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (χ ψ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F)
    (he : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      χ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S) =
      ψ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S)) :
    ∃ c : F, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, MinusculeParameters.nativeFullParameterTriple D F A χ i = c * MinusculeParameters.nativeFullParameterTriple D F A ψ (σ i) := by
  have hvalue (θ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) (k : Fin 4) :
      nativeGL3RationalCharacter D F θ (Minuscule.Local.gl3MinusculeHecke q k) =
        θ (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D A k) :=
    Minuscule.Intrinsic.nativeGL3Character_minuscule D F θ A hg hq hIsogenyQuotient hA k
  have hspec (θ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F) :
      let α := MinusculeParameters.nativeFullParameterTriple D F A θ
      nativeGL3RationalCharacter D F θ (Minuscule.Local.gl3MinusculeHecke q 1) = (q : F) * (α 0 + α 1 + α 2) ∧
      nativeGL3RationalCharacter D F θ (Minuscule.Local.gl3MinusculeHecke q 2) =
        (q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      nativeGL3RationalCharacter D F θ (Minuscule.Local.gl3MinusculeHecke q 3) = α 0 * α 1 * α 2 := by
    simp only [hvalue, MinusculeParameters.nativeMinusculeHecke_three D A hg hq hIsogenyQuotient hA]
    exact (MinusculeParameters.nativeFullParameterTriple_spec D F A θ).2
  apply ProjectiveCharacters.Local.gl3_projective_triples q D.reference.distinguished
    (nativeGL3RationalCharacter D F χ) (nativeGL3RationalCharacter D F ψ) ?_
    (MinusculeParameters.nativeFullParameterTriple D F A χ) (MinusculeParameters.nativeFullParameterTriple D F A ψ) (hspec χ) (hspec ψ)
  intro S
  change χ (1 ⊗ₜ[ℚ] CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished
      (Retraction.Local.sl3ToGL3Hecke q D.reference.distinguished S)) =
    ψ (1 ⊗ₜ[ℚ] CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished
      (Retraction.Local.sl3ToGL3Hecke q D.reference.distinguished S))
  rw [Retraction.Local.sl3ToGL3Hecke_factorization]
  exact he S

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveUniqueness
