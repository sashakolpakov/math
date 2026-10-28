import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.WeightsAsDifferences
import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalChamberRatios
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv

/-! # Exponential Matrix Chamber -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! In split eigenbasis coordinates the exponential is diagonal, and
the standard adjacent diagonal bounds imply intrinsic chamber bounds. -/

open NormedSpace
open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

theorem KillingSplit.Construction.KillingSplitWeightData.exponential_matrix (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis (exp A.val) =
      Matrix.diagonal (fun i => Real.exp (d.weight i A)) := by
  have he : A.val = (BasisSpectralOperator.Construction.basisSpectralEnd d.basis.toBasis (fun i => d.weight i A)).toContinuousLinearMap := by
    have h := BasisSpectralOperator.Construction.basisSpectralEnd_eq_of_eigenbasis d.basis.toBasis (fun i => d.weight i A)
      A.val.toLinearMap (fun i => d.eigenvector i A)
    ext x
    exact (LinearMap.congr_fun h x).symm
  rw [he, SpectralOperatorExponential.Construction.basisSpectralEnd_exp]
  change LinearMap.toMatrix d.basis.toBasis d.basis.toBasis
    (BasisSpectralOperator.Construction.basisSpectralEnd d.basis.toBasis (fun i => exp (d.weight i A))) = _
  simpa only [← Real.exp_eq_exp_ℝ] using
    SpectralOperatorExponential.Construction.basisSpectralEnd_toMatrix d.basis.toBasis (fun i => exp (d.weight i A))

theorem KillingSplit.Construction.KillingSplitWeightData.chamber_of_exponential_adjacent_bounds
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (A : d.subspace)
    (hA : ∀ i j, i.val + 1 = j.val → Real.exp (d.weight i A) ≤ 2 * Real.exp (d.weight j A)) :
    A ∈ d.truncatedNegativeChamber (Real.log ((2 : ℝ) ^ Module.finrank ℝ L)) := by
  apply d.chamber_of_upper_differences hK hd A
  intro i j hij
  apply Real.exp_le_exp.mp
  rw [Real.exp_sub, Real.exp_log (by positivity)]
  exact DiagonalChamberRatios.Construction.positive_gap_chain_ratio (fun r => Real.exp (d.weight r A))
    (fun r => Real.exp_pos _) hA i j hij.le

end

/-! Split endomorphisms are diagonal in their common eigenbasis,
and every row of an invertible matrix has a nonzero entry. -/

open scoped Classical

theorem Split.ExponentialMatrixChamber.Construction.invertible_matrix_row_nonzero {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℝ)ˣ) (i : Fin n) :
    ∃ j, g.val i j ≠ 0 := by
  by_contra! h
  have hd : g.val.det ≠ 0 := isUnit_iff_ne_zero.mp (g.val.isUnit_iff_isUnit_det.mp g.isUnit)
  exact hd (Matrix.det_eq_zero_of_row_eq_zero i h)

theorem KillingSplit.Construction.KillingSplitWeightData.linear_matrix
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis A.val = Matrix.diagonal (fun i => d.weight i A) := by
  have he := BasisSpectralOperator.Construction.basisSpectralEnd_eq_of_eigenbasis d.basis.toBasis (fun i => d.weight i A)
    A.val.toLinearMap (fun i => d.eigenvector i A)
  change LinearMap.toMatrix d.basis.toBasis d.basis.toBasis A.val.toLinearMap = _
  rw [← he, SpectralOperatorExponential.Construction.basisSpectralEnd_toMatrix]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
