import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralParameters

/-! # Normalized Central -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NormalizedCentral

noncomputable section

/-! The full central constraint for any normalized projective parameter,
including the direct root derived from the native dual radial action. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_central_parameter_for_normalized_root
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (fullSide : Fin s → Bool) (j : ParameterChoices.Qbar →+* ℂ) (z : ParameterChoices.Qbar) (hz : z ≠ 0)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hoccurs : (⨅ h : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q,
      (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hprojective : ∃ c : ParameterChoices.Qbar, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ i = c *
        (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, z] : Fin 3 → ParameterChoices.Qbar) (σ i)) :
    let α := MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ
    let C := (1 : ParameterChoices.Qbar) ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide
    ∃ b : ParameterChoices.Qbar, ∃ σ : Equiv.Perm (Fin 3),
      b ≠ 0 ∧ IsAlgebraic ℚ b ∧ (∀ i, IsAlgebraic ℚ (α i)) ∧
      (∀ i, χ C * α i = b *
        (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, z] : Fin 3 → ParameterChoices.Qbar) (σ i)) ∧
      b ^ 3 * z = (χ C) ^ 3 *
        χ (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished) ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1 ∧
        ∀ γ : ParameterChoices.Qbar ≃ₐ[ℚ] ParameterChoices.Qbar, ((γ b) ^ 3 * γ (z)) ^ n = 1) ∧
      χ (C * (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 1)) = (q : ParameterChoices.Qbar) * b *
        (DualRadialSatake.Iwasawa.algebraicSqrt q j + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ + z) ∧
      χ (C ^ 2 * (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 2)) = (q : ParameterChoices.Qbar) * b ^ 2 *
        (DualRadialSatake.Iwasawa.algebraicSqrt q j * (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ +
          DualRadialSatake.Iwasawa.algebraicSqrt q j * z + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ * z) := by
  let : FiniteDimensional ℚ D.pel.H1 := Base.native_betti_finite D hg
  let : Algebra.IsAlgebraic ℚ ParameterChoices.Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  obtain ⟨_, hT₁, hT₂, hT₃⟩ := MinusculeParameters.nativeFullParameterTriple_spec D.pel ParameterChoices.Qbar A χ
  exact CentralParameters.central_constraint_on_full_satake_extensions
    (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A) χ q (Fact.out : q.Prime)
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) z (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) hz
    (Algebra.IsAlgebraic.isAlgebraic _) (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 1)
    (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 2)
    (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished)
    (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide)
    (MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ) hoccurs
    (CentralFinite.native_central_actions_over_finite_order D.pel hg hq hIsogenyQuotient hdegree hTateComparison A hA
      D.pel.reference.distinguished fullSide ParameterChoices.Qbar)
    hT₁ hT₂ hT₃ hprojective

/-- The same three rational operators used by the ordinary Frobenius polynomial. -/
def nativeAbsorbedHecke (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (fullSide : Fin s → Bool) : Fin 3 → AbelianScheme.TateComparison.HeckeKernel.Hecke s q :=
  ![AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide * MinusculeParameters.nativeMinusculeHecke D.pel A 1,
    AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 2 * MinusculeParameters.nativeMinusculeHecke D.pel A 2,
    AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 3 * AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished]

theorem native_absorbed_parameter_values
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (fullSide : Fin s → Bool) (j : ParameterChoices.Qbar →+* ℂ) (z : ParameterChoices.Qbar) (hz : z ≠ 0)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hoccurs : (⨅ h : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q,
      (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hprojective : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) :
    ∃ b : ParameterChoices.Qbar, b ≠ 0 ∧ (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1) ∧
      ∀ i : Fin 3, χ (1 ⊗ₜ[ℚ] nativeAbsorbedHecke D A fullSide i) =
        (![(q : ParameterChoices.Qbar) * b * (DualRadialSatake.Iwasawa.algebraicSqrt q j + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ + z),
          (q : ParameterChoices.Qbar) * b ^ 2 * (DualRadialSatake.Iwasawa.algebraicSqrt q j * (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ +
            DualRadialSatake.Iwasawa.algebraicSqrt q j * z + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ * z),
          b ^ 3 * z] : Fin 3 → ParameterChoices.Qbar) i := by
  obtain ⟨b, _, hb, _, _, _, hdet, ⟨n, hn, hbn, _⟩, h₁, h₂⟩ :=
    native_central_parameter_for_normalized_root D hg hq hIsogenyQuotient hdegree hTateComparison A hA hElementaryDivisors
      fullSide j z hz χ hoccurs hprojective
  refine ⟨b, hb, ⟨n, hn, hbn⟩, ?_⟩
  intro i
  fin_cases i
  · change χ (1 ⊗ₜ[ℚ] (AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide *
      MinusculeParameters.nativeMinusculeHecke D.pel A 1)) =
        (q : ParameterChoices.Qbar) * b * (DualRadialSatake.Iwasawa.algebraicSqrt q j + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ + z)
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using h₁
  · change χ (1 ⊗ₜ[ℚ] (AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 2 *
      MinusculeParameters.nativeMinusculeHecke D.pel A 2)) =
        (q : ParameterChoices.Qbar) * b ^ 2 * (DualRadialSatake.Iwasawa.algebraicSqrt q j * (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ +
          DualRadialSatake.Iwasawa.algebraicSqrt q j * z + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ * z)
    simpa only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
      one_pow, one_mul] using h₂
  · change χ (1 ⊗ₜ[ℚ] (AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide ^ 3 *
      AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished)) = b ^ 3 * z
    simpa only [← map_pow, ← map_mul, Algebra.TensorProduct.tmul_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul] using hdet.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NormalizedCentral
