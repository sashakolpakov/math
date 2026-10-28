import OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarStabilization
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation

/-! # Scalar Power Factorization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization

noncomputable section

/-! Powers of the conjugated rational scalar split into commuting active and auxiliary factors. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)

theorem scalar_active_auxiliary_commute (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) :
    Commute (ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (a μ)⁻¹) (AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a) := by
  apply FinitePadicCommutation.Realization.finitePadicSymplecticInclusion_commute
  rw [AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix_projection q μ S γ a hscalar]
  exact DiagonalPowerBounds.Realization.diagonalSymplectic_commute _ _

theorem scalar_active_auxiliary_factorization (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ) :
    ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (a μ)⁻¹ * AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a =
      AuxiliaryScalarMatrix.Realization.scalarFiniteConjugate q S γ := by
  exact mul_inv_cancel_left _ _

theorem scalar_active_auxiliary_power_factorization (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) (N : ℕ) :
    ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (((a μ)⁻¹) ^ N) * AuxiliaryScalarMatrix.Realization.scalarAuxiliaryMatrix q μ S γ a ^ N =
      AuxiliaryScalarMatrix.Realization.scalarFiniteConjugate q S (γ ^ N) := by
  rw [← ActiveFinitePhase.Realization.activeFiniteSymplectic_pow,
    ← (scalar_active_auxiliary_commute q μ S γ a hscalar).mul_pow,
    scalar_active_auxiliary_factorization]
  change (FiniteConjugation.Realization.finitePadicSymplecticInclusion q S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ *
    (FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹) ^ N = _
  rw [conj_pow, ← map_pow]
  rfl

theorem padic_scalar_norm_power (a : ℚ_[q]ˣ) (M N : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) :
    ‖(a ^ N : ℚ_[q]ˣ).val‖ = (q : ℝ) ^ (-((N * M : ℕ) : ℤ)) := by
  rw [Units.val_pow_eq_pow_val, norm_pow, ha, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPowerFactorization.Realization
