import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.UpperPermutationConjugates
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRPositiveUnit

/-! # Permuted Mixed Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PermutedMixedProduct.Construction

noncomputable section

/-! The normalized mixed product is uniformly compact for an
ambient Siegel family followed by a permutation and an upper unipotent. -/

theorem compact_permuted_siegel_mixed_products
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (Matrix (Fin m) (Fin m) ℝ)ˣ) (hC : IsCompact C)
    (htri : ∀ n ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular n.val) (t : ℝ) (ht : 0 ≤ t)
    (σ : Equiv.Perm (Fin m)) :
    ∃ D : Set (Matrix (Fin m) (Fin m) ℝ)ˣ, IsCompact D ∧
      ∀ (k a v : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ),
        ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ →
        (∀ i, 0 < d i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d →
        (∀ i j, i.val + 1 = j.val → Real.log (d i) - Real.log (d j) ≤ t) →
        UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis v.val) → ∀ n ∈ C,
        let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
        let g := k * a * F.symm n * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) * v
        QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit b g * OperatorQRVal.Construction.operatorQRUnipotentUnit b g * (F v)⁻¹ *
          (QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit b g)⁻¹ ∈ D := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let p := F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
  obtain ⟨Q, hQ, hq⟩ := UpperPermutationConjugates.Construction.compact_upper_permutation_conjugates b C hC htri t ht σ
  obtain ⟨D, hD, hbound⟩ := QRPositiveUnit.Construction.compact_operatorQR_normalized_mixed_products b Q hQ
  refine ⟨D, hD, fun k a v d hk hd ha hstep hv n hn => ?_⟩
  let q := a * F.symm n * a⁻¹ * p
  let ap := p⁻¹ * a * p
  have hqQ : q ∈ Q := hq a d hd ha hstep n hn
  have hap : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis ap.val = Matrix.diagonal (fun i => d (σ.symm i)) :=
    UpperPermutationConjugates.Construction.operator_permutation_conjugate_diagonal b a σ d ha
  have he : k * a * F.symm n * p * v = k * (q * ap * v) := by dsimp only [q, ap]; group
  change QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit b (k * a * F.symm n * p * v) *
      OperatorQRVal.Construction.operatorQRUnipotentUnit b (k * a * F.symm n * p * v) * (F v)⁻¹ *
      (QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit b (k * a * F.symm n * p * v))⁻¹ ∈ D
  rw [he, QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit_left_orthogonal b k _ hk,
    QRPositiveUnit.Construction.operatorQRUnipotentUnit_left_orthogonal b k _ hk]
  exact hbound q hqQ ap v _ (fun i => hd (σ.symm i)) hap hv

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PermutedMixedProduct.Construction
