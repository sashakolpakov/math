import OAI.RepresentationTheory.Hecke.RadialDilation.ActiveFinitePhase
import OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalPowerBounds
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteScalarProjection
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime

/-! # Auxiliary Scalar Matrix -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization

noncomputable section

/-! Removing the active diagonal factor from the conjugated rational scalar. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)

def scalarFiniteConjugate (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) :
    Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) Theta.PoissonAutomorphyNormalizationData.AQf :=
  FiniteConjugation.Realization.finitePadicSymplecticInclusion q S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ *
    (FiniteConjugation.Realization.finitePadicSymplecticInclusion q S)⁻¹

def scalarAuxiliaryMatrix (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ) : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) Theta.PoissonAutomorphyNormalizationData.AQf :=
  (ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (a μ)⁻¹)⁻¹ * scalarFiniteConjugate q S γ

omit μ in
theorem scalarFiniteConjugate_projection (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom (scalarFiniteConjugate q S γ) =
      DiagonalPowerBounds.Realization.diagonalSymplectic (fun i : Place × Fin 3 => a i.1) := by
  unfold scalarFiniteConjugate
  rw [FiniteConjugation.Realization.finiteSymplectic_conjugation_projection]
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [FiniteScalarProjection.Realization.symplectic_conjugation_action S _ _ hscalar, DiagonalPowerBounds.Realization.diagonalSymplectic_action]
  simp only [ScalarPhase.Realization.pairedScalarPhase, Units.val_inv_eq_inv_val]

theorem scalarAuxiliaryMatrix_projection (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (hscalar : ∀ x, S.val *ᵥ ((Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val *ᵥ x) =
      ScalarPhase.Realization.pairedScalarPhase q a (S.val *ᵥ x)) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom (scalarAuxiliaryMatrix q μ S γ a) =
      DiagonalPowerBounds.Realization.diagonalSymplectic (DiagonalPowerBounds.Realization.auxiliaryCoordinateUnits μ a) := by
  change Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom
    ((ActiveFinitePhase.Realization.activeFiniteSymplectic q μ (a μ)⁻¹)⁻¹ * scalarFiniteConjugate q S γ) = _
  rw [map_mul, map_inv, scalarFiniteConjugate_projection q S γ a hscalar]
  change (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom (FiniteConjugation.Realization.finitePadicSymplecticInclusion q
    (DiagonalPowerBounds.Realization.diagonalSymplectic (DiagonalUnits.Realization.activeCoordinateUnits μ ((a μ)⁻¹)⁻¹))))⁻¹ * _ = _
  rw [inv_inv, FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection,
    ← DiagonalPowerBounds.Realization.active_auxiliary_diagonal_factorization μ a, inv_mul_cancel_left]

theorem scalarAuxiliaryMatrix_other_place (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (v : HeightOneSpectrum ℤ) (hv : v ≠ FiniteSchur.Realization.rationalPrime q) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (scalarAuxiliaryMatrix q μ S γ a) =
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ) := by
  unfold scalarAuxiliaryMatrix scalarFiniteConjugate ActiveFinitePhase.Realization.activeFiniteSymplectic
  simp only [map_mul, map_inv, FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_place q v hv,
    inv_one, one_mul, mul_one]

theorem scalarAuxiliaryMatrix_other_prime (S : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ_[q])
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) ℚ) (a : Place → ℚ_[q]ˣ)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection p).toRingHom (scalarAuxiliaryMatrix q μ S γ a) =
      Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) γ := by
  unfold scalarAuxiliaryMatrix scalarFiniteConjugate ActiveFinitePhase.Realization.activeFiniteSymplectic
  simp only [map_mul, map_inv, FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq,
    inv_one, one_mul, mul_one, FiniteConjugation.Realization.rationalSymplectic_finite_projection]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.AuxiliaryScalarMatrix.Realization
