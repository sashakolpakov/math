import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectorRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.DualOccurrence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DualRadialRestriction

/-! # Projected Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedRadial.Intrinsic

noncomputable section

/-! A nonzero projection of the radial theta family supplies the parameter
of that same full algebraic Hecke character. Both its occurrence and its
initial projective triple are conclusions of the construction. -/

open scoped Classical TensorProduct _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.DualOccurrence.Iwasawa
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_full_projected_dual_radial_parameter
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)
    (M : ℕ) (hM : 0 < M) (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) =
      Intrinsic.Spectrum.nativeActiveHeckeActionOver D ℂ A
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished) T (Θ b))
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] ParameterChoices.Qbar)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (hP : ∀ h, Commute P ((A.cohomologyAction h).baseChange ℂ))
    (hspace : LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ)
      (fun h => j (χ h)))
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (hne : P (Θ b) ≠ 0) :
    ∃ a : ParameterChoices.Qbarˣ, (a : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (a : ParameterChoices.Qbar))‖ = 1) ∧
      HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D.pel ParameterChoices.Qbar A)
        (ChosenOccurrence.Spectral.fullCharacterOfRational (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) ≠ ⊥ ∧
      ∃ c : ParameterChoices.Qbar, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
        ∀ i, Intrinsic.MinusculeParameters.nativeFullParameterTriple D.pel ParameterChoices.Qbar A
          (ChosenOccurrence.Spectral.fullCharacterOfRational (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) i =
            c * (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, (a : ParameterChoices.Qbar)] : Fin 3 → ParameterChoices.Qbar) (σ i) := by
  let eH := RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished
  let χC : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] ℂ := j.toRatAlgHom.comp χ
  obtain ⟨a, ha, hnorm, hchar, _⟩ := Radial.DualOccurrence.Iwasawa.projected_dual_radial_occurring_satake q hElementaryDivisors
    (Intrinsic.Spectrum.nativeActiveHeckeActionOver D ℂ A eH) Θ M hM j ω hω hrelation hHecke
    (ProjectorRestriction.Intrinsic.nativeActiveComplexCharacter D eH χC) P (ProjectorRestriction.Intrinsic.native_projector_active_commute D A eH P hP)
    (ProjectorRestriction.Intrinsic.native_projector_active_space D A eH hElementaryDivisors χC P hspace) b hne
  refine ⟨a, ha, hnorm, ?_, ?_⟩
  · apply ChosenOccurrence.Intrinsic.native_chosen_full_occurrence D hg hElementaryDivisors A j χ
    exact (Submodule.ne_bot_iff _).mpr ⟨P (Θ b), hspace (LinearMap.mem_range_self P (Θ b)), hne⟩
  · apply Intrinsic.DualRadialRestriction.native_full_dual_radial_projective D.pel A hg hq hIsogenyQuotient hA j a
      (ChosenOccurrence.Spectral.fullCharacterOfRational (F := ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ)
    intro S
    have h := DFunLike.congr_fun hchar ((1 : ℂ) ⊗ₜ[ℚ] S)
    simp only [ProjectorRestriction.Intrinsic.nativeActiveComplexCharacter, ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul,
      AlgHom.comp_apply, χC, eH] at h
    rw [ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul]
    exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedRadial.Intrinsic
