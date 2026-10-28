import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationMatrixUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRLogTranslation

/-! # QR Permutation Log Formula -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRPermutationLogFormula.Construction

noncomputable section

/-! Logarithmic QR coordinates after a permutation are the permuted
input diagonal plus the QR logarithm of a conjugated unipotent factor. -/

theorem operatorQRLogDiagonal_permutation_formula
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (a n : (L →L[ℝ] L)ˣ)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) (i : Fin m) :
    let p := (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
    OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n * p) i =
      OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n * a⁻¹ * p) i + Real.log (d (σ.symm i)) := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let p := F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
  let q := a * n * a⁻¹ * p
  let ap := p⁻¹ * a * p
  have hp : F p = PermutationMatrixUnits.Construction.permutationMatrixUnit σ := F.apply_symm_apply _
  have hap : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis ap.val = Matrix.diagonal (fun i => d (σ.symm i)) := by
    change (F ap).val = _
    have he : F ap = (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹ * F a * PermutationMatrixUnits.Construction.permutationMatrixUnit σ := by
      simp only [ap, map_mul, map_inv, hp]
    rw [he]
    change (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹.val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val *
      (PermutationMatrixUnits.Construction.permutationMatrixUnit σ).val = _
    rw [ha]
    exact PermutationMatrixUnits.Construction.permutationMatrixUnit_conjugate_diagonal σ d
  have hg : a * n * p = q * ap := by dsimp only [q, ap]; group
  change OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n * p) i = OperatorQRVal.Construction.operatorQRLogDiagonal b q i + _
  rw [hg]
  exact OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_right_diagonal b q ap _ (fun i => hd (σ.symm i)) hap i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRPermutationLogFormula.Construction
