import OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix
import OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryStabilization

/-! # Auxiliary Scalar Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization.Realization

noncomputable section

/-! The explicit auxiliary scalar has a uniform radial eigenphase after a positive power. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)

theorem auxiliary_diagonal_fixes_localBlock (a : Place → ℚ_[q]ˣ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    (DiagonalPowerBounds.Realization.diagonalSymplectic (DiagonalPowerBounds.Realization.auxiliaryCoordinateUnits μ a)).val *ᵥ FinitePhaseProjection.Realization.localBlockPhase q μ v =
      FinitePhaseProjection.Realization.localBlockPhase q μ v := by
  rw [DiagonalPowerBounds.Realization.diagonalSymplectic_action]
  funext i
  cases i with
  | inl i =>
      by_cases hi : i.1 = μ <;> simp [FinitePhaseProjection.Realization.localBlockPhase, DiagonalPowerBounds.Realization.auxiliaryCoordinateUnits, hi]
  | inr i =>
      by_cases hi : i.1 = μ <;> simp [FinitePhaseProjection.Realization.localBlockPhase, DiagonalPowerBounds.Realization.auxiliaryCoordinateUnits, hi]

theorem scalarAuxiliaryMatrix_fixes_active (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) (p s : Mem.Realization.Position q) :
    (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a).val *ᵥ
      Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) =
        Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ p) (FiniteBlockChart.Realization.finiteBlockInclusion q μ s) := by
  change (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a).val *ᵥ FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Sum.elim s p) =
    FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (Sum.elim s p)
  apply FinitePhaseProjection.Realization.finiteMatrix_localBlock_action q μ _ id
  intro v
  have hm := congrArg Subtype.val (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_projection q μ S γ a hscalar)
  change (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a).val.map (FiniteSchur.Realization.finitePadicProjection q) = _ at hm
  rw [hm]
  exact auxiliary_diagonal_fixes_localBlock q μ a v

theorem scalarAuxiliaryMatrix_power_bounds (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R) :
    ∀ (p : ℕ) [Fact p.Prime], ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection p).toRingHom (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a)) ^ N).val i j‖ ≤ R := by
  intro p hp
  by_cases hpq : p = q
  · subst p
    refine ⟨1, ?_⟩
    intro N i j
    rw [AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_projection q μ S γ a hscalar]
    exact DiagonalPowerBounds.Realization.diagonalSymplectic_unit_power_bound _ (DiagonalPowerBounds.Realization.auxiliaryCoordinateUnits_norm μ a ha) N i j
  · rw [AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_other_prime q μ S γ a p hpq]
    exact haway p hpq

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem exists_scalar_auxiliary_power_radial_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)
    (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x))
    (ha : ∀ τ, τ ≠ μ → ‖(a τ : ℚ_[q])‖ = 1)
    (haway : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ,
      ∀ (N : ℕ) i j, ‖((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ) ^ N).val i j‖ ≤ R) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : MpF,
      D.finite.project m = AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a ^ N →
      ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
        D.finite.action m (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b) =
          ξ • Canonical.Realization.canonicalFiniteRadialEmbedding q μ b := by
  apply AuxiliaryStabilization.Realization.exists_auxiliary_power_uniform_radial_phase q μ hLocalWeil D
    (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a) γ {FiniteSchur.Realization.rationalPrime q}
  · intro v hv
    exact AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_other_place q μ S γ a v (by simpa only [Finset.mem_singleton] using hv)
  · exact scalarAuxiliaryMatrix_power_bounds q μ S γ a hscalar ha haway
  · exact scalarAuxiliaryMatrix_fixes_active q μ S γ a hscalar

end

end OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization.Realization
