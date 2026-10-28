import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MinusculeValues
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectiveUniqueness

/-! # Torus Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction

noncomputable section

/-! Identify the actual chosen native full triple from its actual SL3
torus-character restriction. The inverse coordinates are forced by the
proved raw minuscule normalization. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MinusculeValues.Iwasawa

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (F : Type*) [Field F] [CharZero F] [Algebra ℚ F] [IsAlgClosed F]

theorem native_full_projective_torus_restriction (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (j : F →ₐ[ℚ] ℂ) (t : Fin 3 → Fˣ) (χ : F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] F)
    (he : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      χ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S) = SatakeBaseChange.Iwasawa.torusSatakeOver q t S) :
    ∃ c : F, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, MinusculeParameters.nativeFullParameterTriple D F A χ i = c * (t (σ i) : F)⁻¹ := by
  have hvalue (k : Fin 4) : ProjectiveUniqueness.nativeGL3RationalCharacter D F χ (Minuscule.Local.gl3MinusculeHecke q k) =
      χ (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D A k) :=
    Minuscule.Intrinsic.nativeGL3Character_minuscule D F χ A hg hq hIsogenyQuotient hA k
  have hspec : let α := MinusculeParameters.nativeFullParameterTriple D F A χ
      ProjectiveUniqueness.nativeGL3RationalCharacter D F χ (Minuscule.Local.gl3MinusculeHecke q 1) = (q : F) * (α 0 + α 1 + α 2) ∧
      ProjectiveUniqueness.nativeGL3RationalCharacter D F χ (Minuscule.Local.gl3MinusculeHecke q 2) =
        (q : F) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ∧
      ProjectiveUniqueness.nativeGL3RationalCharacter D F χ (Minuscule.Local.gl3MinusculeHecke q 3) = α 0 * α 1 * α 2 := by
    simp only [hvalue, MinusculeParameters.nativeMinusculeHecke_three D A hg hq hIsogenyQuotient hA]
    exact (MinusculeParameters.nativeFullParameterTriple_spec D F A χ).2
  apply ProjectiveCharacters.Local.gl3_projective_triples q D.reference.distinguished
    (ProjectiveUniqueness.nativeGL3RationalCharacter D F χ) (TorusCharacters.Iwasawa.gl3TorusSatakeOver q t) ?_
    (MinusculeParameters.nativeFullParameterTriple D F A χ) (fun i => (t i : F)⁻¹) hspec
    (MinusculeValues.Iwasawa.gl3TorusSatakeOver_minuscule_over q j t)
  intro S
  change χ (1 ⊗ₜ[ℚ] CosetsKernel.Local.activeGL3HeckeMap q D.reference.distinguished
    (Retraction.Local.sl3ToGL3Hecke q D.reference.distinguished S)) = _
  rw [Retraction.Local.sl3ToGL3Hecke_factorization, TorusCharacters.Iwasawa.gl3TorusSatakeOver_sl3]
  exact he S

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction
