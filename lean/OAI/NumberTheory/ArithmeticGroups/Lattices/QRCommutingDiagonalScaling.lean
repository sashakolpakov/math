import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRUnipotentTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates

/-! # QR Commuting Diagonal Scaling -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRCommutingDiagonalScaling.Construction

noncomputable section

section

/-! A diagonal commuting with the unipotent QR factor leaves that
factor unchanged under right scaling. -/

theorem operatorQRUnipotent_right_diagonal_of_commute
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g a : (L →L[ℝ] L)ˣ)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d)
    (hc : Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal d)) :
    OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * a) = OperatorQRVal.Construction.operatorQRUnipotentMatrix b g := by
  rw [(OperatorQRDiagonalTranslation.Construction.operatorQR_right_diagonal b g a d hd ha).2.2, mul_assoc, hc.eq, ← mul_assoc,
    Matrix.diagonal_mul_diagonal]
  have he : Matrix.diagonal (fun i => (d i)⁻¹ * d i) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simp only [inv_mul_cancel₀ (ne_of_gt (hd _)), Matrix.diagonal_one]
  rw [he, one_mul]

theorem operatorQRUnipotentUnit_right_diagonal_unipotent
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g a n : (L →L[ℝ] L)ˣ)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d)
    (hc : Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal d))
    (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * a * n) =
      OperatorQRVal.Construction.operatorQRUnipotentUnit b g * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis n := by
  apply Units.ext
  change (OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * a * n)).val =
    (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val
  rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQRUnipotentUnit_val,
    (OperatorQRUnipotentTranslation.Construction.operatorQR_right_unipotent b (g * a) n hn).2.2,
    operatorQRUnipotent_right_diagonal_of_commute b g a d hd ha hc]

end

/-! Compact factors give a uniform unipotent QR bound after every
positive diagonal scaling that commutes with the core QR factor. -/

open scoped Pointwise

theorem operatorQR_compact_commuting_scaling_bound
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C N : Set (L →L[ℝ] L)ˣ) (hC : IsCompact C) (hN : IsCompact N)
    (htri : ∀ n ∈ N, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ C, ∀ n ∈ N, ∀ a : (L →L[ℝ] L)ˣ, ∀ d : Fin m → ℝ,
      (∀ i, 0 < d i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d →
      Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal d) →
      ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * a * n) i j| ≤ c := by
  let S := (OperatorQRVal.Construction.operatorQRUnipotentUnit b '' C) * (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis '' N)
  have hS : IsCompact S :=
    (hC.image (OperatorQRVal.Construction.operatorQRUnipotentUnit_continuous b)).mul
      (hN.image (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).continuous)
  obtain ⟨c, hc, hb⟩ := Compact.TriangularConjugates.Construction.compact_matrix_unit_entries_bound S hS
  refine ⟨c, hc, fun g hg n hn a d hd ha hcomm i j => ?_⟩
  have hs : OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * a * n) ∈ S := by
    rw [operatorQRUnipotentUnit_right_diagonal_unipotent b g a n d hd ha hcomm (htri n hn)]
    exact Set.mem_mul.mpr ⟨_, ⟨g, hg, rfl⟩, _, ⟨n, hn, rfl⟩, rfl⟩
  simpa only [OperatorQRVal.Construction.operatorQRUnipotentUnit_val] using hb _ hs i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRCommutingDiagonalScaling.Construction
