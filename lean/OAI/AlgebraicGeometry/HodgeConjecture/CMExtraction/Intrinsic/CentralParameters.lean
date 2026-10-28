import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Central Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralParameters

noncomputable section

/-! Apply the complete CentralConstraint to the actual full native Betti action and
the inverse dilation root, with central finite order proved by CentralAction.
The normalized triple is constructed from the actual minuscule operators.
Full occurrence and identification of its projective restriction remain
the explicit local-parameter inputs. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake.Iwasawa

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_central_parameter_constraint
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (fullSide : Fin s → Bool) (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ)
    (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (hoccurs : (⨅ h : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q,
      (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hprojective : ∃ c : ParameterChoices.Qbar, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ i = c *
        (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, (a : ParameterChoices.Qbar)⁻¹] : Fin 3 → ParameterChoices.Qbar) (σ i)) :
    let α := MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ
    let C := (1 : ParameterChoices.Qbar) ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide
    ∃ b : ParameterChoices.Qbar, ∃ σ : Equiv.Perm (Fin 3),
      b ≠ 0 ∧ IsAlgebraic ℚ b ∧ (∀ i, IsAlgebraic ℚ (α i)) ∧
      (∀ i, χ C * α i = b *
        (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, (a : ParameterChoices.Qbar)⁻¹] : Fin 3 → ParameterChoices.Qbar) (σ i)) ∧
      b ^ 3 * (a : ParameterChoices.Qbar)⁻¹ = (χ C) ^ 3 *
        χ (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished) ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * (a : ParameterChoices.Qbar)⁻¹) ^ n = 1 ∧
        ∀ γ : ParameterChoices.Qbar ≃ₐ[ℚ] ParameterChoices.Qbar, ((γ b) ^ 3 * γ ((a : ParameterChoices.Qbar)⁻¹)) ^ n = 1) ∧
      χ (C * (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 1)) = (q : ParameterChoices.Qbar) * b *
        (DualRadialSatake.Iwasawa.algebraicSqrt q j + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ + (a : ParameterChoices.Qbar)⁻¹) ∧
      χ (C ^ 2 * (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 2)) = (q : ParameterChoices.Qbar) * b ^ 2 *
        (DualRadialSatake.Iwasawa.algebraicSqrt q j * (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ +
          DualRadialSatake.Iwasawa.algebraicSqrt q j * (a : ParameterChoices.Qbar)⁻¹ + (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹ * (a : ParameterChoices.Qbar)⁻¹) := by
  let : FiniteDimensional ℚ D.pel.H1 := Base.native_betti_finite D hg
  let : Algebra.IsAlgebraic ℚ ParameterChoices.Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  obtain ⟨_, hT₁, hT₂, hT₃⟩ := MinusculeParameters.nativeFullParameterTriple_spec D.pel ParameterChoices.Qbar A χ
  exact CentralParameters.central_constraint_on_full_satake_extensions
    (CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A) χ q (Fact.out : q.Prime)
    (DualRadialSatake.Iwasawa.algebraicSqrt q j) (a : ParameterChoices.Qbar)⁻¹ (DualRadialSatake.Iwasawa.algebraicSqrt_sq q j) (inv_ne_zero a.ne_zero)
    (Algebra.IsAlgebraic.isAlgebraic _) (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 1)
    (1 ⊗ₜ[ℚ] MinusculeParameters.nativeMinusculeHecke D.pel A 2)
    (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.pel.reference.distinguished)
    (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.pel.reference.distinguished fullSide)
    (MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A χ) hoccurs
    (CentralFinite.native_central_actions_over_finite_order D.pel hg hq hIsogenyQuotient hdegree hTateComparison A hA
      D.pel.reference.distinguished fullSide ParameterChoices.Qbar)
    hT₁ hT₂ hT₃ hprojective

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralParameters
