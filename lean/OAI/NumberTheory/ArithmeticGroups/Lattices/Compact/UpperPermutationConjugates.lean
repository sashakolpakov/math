import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationLogControl

/-! # Upper Permutation Conjugates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.UpperPermutationConjugates.Construction

noncomputable section

/-! Compact containers for a bounded upper unipotent family after
conjugation by chamber diagonals and a fixed permutation. -/

theorem compact_upper_permutation_conjugates
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (Matrix (Fin m) (Fin m) ℝ)ˣ) (hC : IsCompact C)
    (htri : ∀ n ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular n.val) (t : ℝ) (ht : 0 ≤ t)
    (σ : Equiv.Perm (Fin m)) :
    ∃ Q : Set (L →L[ℝ] L)ˣ, IsCompact Q ∧ ∀ a : (L →L[ℝ] L)ˣ, ∀ d : Fin m → ℝ,
      (∀ i, 0 < d i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d →
      (∀ i j, i.val + 1 = j.val → Real.log (d i) - Real.log (d j) ≤ t) → ∀ n ∈ C,
      a * (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm n * a⁻¹ *
        (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) ∈ Q := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let P := PermutationMatrixUnits.Construction.permutationMatrixUnit σ
  obtain ⟨D, hD, hb⟩ := TriangularConjugates.Construction.compact_upper_diagonal_conjugates C hC htri
    (Real.exp ((m : ℝ) * t)) (Real.exp_pos _).le
  refine ⟨(fun M => F.symm (M * P)) '' D,
    hD.image (F.symm.continuous.comp (continuous_id.mul continuous_const)), fun a d hd ha hstep n hn => ?_⟩
  have hmem : F a * n * (F a)⁻¹ ∈ D := hb d hd
    (QRCompactLogBounds.Construction.positive_diagonal_ratio_of_log_gaps d hd t ht hstep) (F a) ha n hn
  refine ⟨_, hmem, ?_⟩
  change F.symm ((F a * n * (F a)⁻¹) * P) = a * F.symm n * a⁻¹ * F.symm P
  apply F.injective
  simp only [F.apply_symm_apply, map_mul, map_inv]

theorem operator_permutation_conjugate_diagonal
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (a : (L →L[ℝ] L)ˣ)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) :
    let p := (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (p⁻¹ * a * p).val = Matrix.diagonal (fun i => d (σ.symm i)) := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let p := F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
  change (F (p⁻¹ * a * p)).val = _
  have he : F (p⁻¹ * a * p) = (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹ * F a * PermutationMatrixUnits.Construction.permutationMatrixUnit σ := by
    simp only [p, map_mul, map_inv, F.apply_symm_apply]
  rw [he]
  change (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹.val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val *
    (PermutationMatrixUnits.Construction.permutationMatrixUnit σ).val = _
  rw [ha]
  exact PermutationMatrixUnits.Construction.permutationMatrixUnit_conjugate_diagonal σ d

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.UpperPermutationConjugates.Construction
