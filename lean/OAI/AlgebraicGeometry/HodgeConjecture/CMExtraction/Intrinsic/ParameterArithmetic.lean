import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NormalizedCentral
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterValuations
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ConjugateOccurrence

/-! # Parameter Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterArithmetic

noncomputable section

/-! The same occurring full character has normalized parameters and
central scalars at every conjugate, with the exact three rational Hecke
values required by the ordinary Frobenius polynomial. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

theorem native_conjugate_parameter_arithmetic
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (fullSide : Fin s → Bool) (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbar)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hnorm : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ a)‖ = 1)
    (hocc : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A) χ ≠ ⊥)
    (hproj : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ)
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) a)) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      let Ψ := ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ
      ∃ z b : ParameterChoices.Qbar,
        z ≠ 0 ∧ b ≠ 0 ∧ (∀ γ : Gal(ParameterChoices.Qbar/ℚ), ‖j (γ z)‖ = 1) ∧
        RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A Ψ)
          (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (DualRadialSatake.Iwasawa.algebraicSqrt q j) z) ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1) ∧
        ∀ i : Fin 3, Ψ (1 ⊗ₜ[ℚ] NormalizedCentral.nativeAbsorbedHecke D A fullSide i) =
          (![(q : ParameterChoices.Qbar) * b * (DualRadialSatake.Iwasawa.algebraicSqrt q j + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ + z),
            (q : ParameterChoices.Qbar) * b ^ 2 * (DualRadialSatake.Iwasawa.algebraicSqrt q j * (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ +
              DualRadialSatake.Iwasawa.algebraicSqrt q j * z + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ * z),
            b ^ 3 * z] : Fin 3 → ParameterChoices.Qbar) i := by
  intro σ
  obtain ⟨z, hz⟩ := RepresentationTheory.Hecke.GaloisValuationCm.normalize_conjugate_triple q (DualRadialSatake.Iwasawa.algebraicSqrt q j) a
    (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) σ
  have hp := RepresentationTheory.Hecke.GaloisValuationCm.projective_trans
    (ParameterValuations.native_full_projective_conjugate D.pel A χ _ hproj σ) hz
  have hn := (ParameterValuations.native_normalized_conjugate_root D.pel A χ j a hnorm hproj σ z hp).2
  have hz0 : z ≠ 0 := by
    intro he
    have h := hn 1
    simp [he] at h
  have ho := ConjugateOccurrence.Intrinsic.native_conjugate_full_occurs D.pel hElementaryDivisors ParameterChoices.Qbar A χ σ hocc
  obtain ⟨b, hb, hc, hvals⟩ := NormalizedCentral.native_absorbed_parameter_values D hg hq hIsogenyQuotient hdegree hTateComparison
    A hA hElementaryDivisors fullSide j z hz0
    (ParameterConjugation.Central.conjugateFullCharacter (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ σ) ho hp
  exact ⟨z, b, hz0, hb, hn, hp, hc, hvals⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterArithmetic
