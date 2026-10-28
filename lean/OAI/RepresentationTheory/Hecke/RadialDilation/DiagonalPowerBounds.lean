import OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap

/-! # Diagonal Power Bounds -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalPowerBounds.Realization

noncomputable section

section

/-! Coordinatewise paired scalars form an explicit symplectic group homomorphism. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def diagonalSymplectic : (I → Kˣ) →* Theta.PoissonAutomorphyNormalizationData.Sp I K where
  toFun a := QuadraticCommutator.Realization.ringLevi (DiagonalUnits.Realization.diagonalUnitMatrix a)
  map_one' := by
    apply Subtype.ext
    simp [QuadraticCommutator.Realization.ringLevi, DiagonalUnits.Realization.diagonalUnitMatrix, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext
    simp [QuadraticCommutator.Realization.ringLevi, DiagonalUnits.Realization.diagonalUnitMatrix, Matrix.diagonal_mul_diagonal, mul_comm]

theorem diagonalSymplectic_matrix (a : I → Kˣ) :
    (diagonalSymplectic a).val = Matrix.fromBlocks (Matrix.diagonal (fun i => (a i : K))) 0 0
      (Matrix.diagonal (fun i => ((a i)⁻¹ : Kˣ).val)) := by
  change Matrix.fromBlocks _ _ _ (Matrix.diagonal _).transpose = _
  rw [Matrix.diagonal_transpose]
  rfl

theorem diagonalSymplectic_action (a : I → Kˣ) (x : Sum I I → K) :
    (diagonalSymplectic a).val *ᵥ x =
      Sum.elim (fun i => (a i : K) * x (Sum.inl i))
        (fun i => ((a i)⁻¹ : Kˣ).val * x (Sum.inr i)) := by
  rw [diagonalSymplectic_matrix, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  funext i
  cases i <;> exact Matrix.mulVec_diagonal _ _ _

theorem diagonalSymplectic_pow (a : I → Kˣ) (N : ℕ) :
    diagonalSymplectic a ^ N = diagonalSymplectic (fun i => a i ^ N) :=
  (map_pow diagonalSymplectic a N).symm

theorem diagonalSymplectic_commute (a b : I → Kˣ) :
    Commute (diagonalSymplectic a) (diagonalSymplectic b) :=
  (Commute.all a b).map diagonalSymplectic

theorem reindexed_swapped_diagonal_levi {J : Type*} [Fintype J] [DecidableEq J]
    {F : Type} [Field F] {n : ℕ} (e : J ≃ Fin n) (a : J → Fˣ) :
    PositionReindex.Realization.symplecticReindex e.symm (SymplecticSwap.Realization.symplecticSwapHom
      (Weil.Local.Generators.Construction.leviSymplectic (DiagonalUnits.Realization.diagonalUnitMatrix (fun i => a (e.symm i))))) =
      diagonalSymplectic (fun i => (a i)⁻¹) := by
  apply Subtype.ext
  rw [diagonalSymplectic_matrix]
  apply Matrix.ext
  intro i j
  change (SymplecticSwap.Realization.symplecticSwapHom (Weil.Local.Generators.Construction.leviSymplectic (DiagonalUnits.Realization.diagonalUnitMatrix
    (fun i => a (e.symm i))))).val ((e.sumCongr e) i) ((e.sumCongr e) j) = _
  rw [show (SymplecticSwap.Realization.symplecticSwapHom (Weil.Local.Generators.Construction.leviSymplectic (DiagonalUnits.Realization.diagonalUnitMatrix
    (fun i => a (e.symm i))))).val = Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (Weil.Local.Generators.Construction.leviSymplectic (DiagonalUnits.Realization.diagonalUnitMatrix
    (fun i => a (e.symm i)))).val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap from rfl]
  rw [Weil.Local.Generators.Construction.leviSymplectic_matrix, Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation]
  cases i <;> cases j <;>
    simp [DiagonalUnits.Realization.diagonalUnitMatrix, Matrix.fromBlocks, Matrix.diagonal]
  split_ifs <;> simp_all

end

/-! Paired unit-norm scalars have uniformly bounded powers. -/

open scoped Classical _root_.Matrix

theorem diagonalSymplectic_unit_power_bound {I K : Type*} [Fintype I] [DecidableEq I]
    [NormedField K] (a : I → Kˣ) (ha : ∀ i, ‖(a i : K)‖ = 1) (N : ℕ)
    (i j : Sum I I) : ‖(diagonalSymplectic a ^ N).val i j‖ ≤ 1 := by
  rw [diagonalSymplectic_pow, diagonalSymplectic_matrix]
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.diagonal, Units.val_pow_eq_pow_val]
  all_goals split_ifs <;> simp [norm_pow, norm_inv, ha]

def auxiliaryCoordinateUnits {Place K : Type*} [DecidableEq Place] [Monoid K]
    (μ : Place) (a : Place → Kˣ) : Place × Fin 3 → Kˣ :=
  fun i => if i.1 = μ then 1 else a i.1

theorem active_auxiliary_diagonal_factorization {Place K : Type*}
    [Fintype Place] [DecidableEq Place] [CommRing K] (μ : Place) (a : Place → Kˣ) :
    diagonalSymplectic (DiagonalUnits.Realization.activeCoordinateUnits μ (a μ)) *
      diagonalSymplectic (auxiliaryCoordinateUnits μ a) =
      diagonalSymplectic (fun i : Place × Fin 3 => a i.1) := by
  rw [← map_mul]
  congr 1
  funext i
  by_cases hi : i.1 = μ <;> simp [DiagonalUnits.Realization.activeCoordinateUnits, auxiliaryCoordinateUnits, hi]

theorem auxiliaryCoordinateUnits_norm {Place K : Type*} [DecidableEq Place] [NormedField K]
    (μ : Place) (a : Place → Kˣ) (ha : ∀ τ, τ ≠ μ → ‖(a τ : K)‖ = 1) :
    ∀ i, ‖(auxiliaryCoordinateUnits μ a i : K)‖ = 1 := by
  intro i
  by_cases hi : i.1 = μ <;> simp [auxiliaryCoordinateUnits, hi, ha]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalPowerBounds.Realization
