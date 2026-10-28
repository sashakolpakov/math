import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationSiegelPoint
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRCommutingDiagonalScaling

/-! # Permutation Approximation QR Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationApproximationQRBound.Construction

noncomputable section

section

/-! A uniformly bounded displacement from a common chamber gives
a uniform QR unipotent bound after translation by a permutation. -/

open scoped Pointwise

theorem compact_permutation_qr_bound_of_approximation
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (σ : Equiv.Perm (Fin m))
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C) (aBound : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin m → ℝ, ∀ n ∈ C, ∀ y : Fin m → ℝ,
      Monotone y → Monotone (y ∘ σ.symm) →
      (∀ i, 0 ≤ x i - y i ∧ x i - y i ≤ aBound) →
      ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b (PermutationSiegelPoint.Construction.permutationSiegelPoint b σ x n) i j| ≤ c := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let P := PermutationMatrixUnits.Construction.permutationMatrixUnit σ
  obtain ⟨u, v, hu, hv, hf⟩ := UpperMatrixPermutationFactors.Construction.upper_matrix_continuous_permutation_factors m σ
  let A := Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit '' Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) aBound)
  let D := (A * (u '' C)) * {P}
  let N := (fun n => P⁻¹ * v n * P) '' C
  have hA : IsCompact A := Compact.ExponentialDiagonals.Construction.compact_exponential_diagonals m aBound
  have hD : IsCompact D := (hA.mul (hC.image hu)).mul isCompact_singleton
  have hN : IsCompact N := hC.image ((continuous_const.mul hv).mul continuous_const)
  have htri : ∀ n ∈ F.symm '' N, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val) := by
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular ((F (F.symm (P⁻¹ * v n * P))).val)
    rw [F.apply_symm_apply]
    exact PermutationFactorCentralizer.Construction.permutation_preserved_support_upper σ (v n).val (hf n).2.1 (hf n).2.2.2.1
  obtain ⟨c, hc, hb⟩ := QRCommutingDiagonalScaling.Construction.operatorQR_compact_commuting_scaling_bound b (F.symm '' D) (F.symm '' N)
    (hD.image F.symm.continuous) (hN.image F.symm.continuous) htri
  refine ⟨c, hc, fun x n hn y hy hyσ hxy i j => ?_⟩
  obtain ⟨_, _, hus, _, hfact⟩ := hf n
  let g₀ := F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * u n * P)
  let a₀ := F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (y ∘ σ.symm))
  let n₀ := F.symm (P⁻¹ * v n * P)
  have hg₀ : g₀ ∈ F.symm '' D := by
    refine ⟨_, ?_, rfl⟩
    apply Set.mem_mul.mpr
    refine ⟨_, ?_, P, Set.mem_singleton P, rfl⟩
    apply Set.mem_mul.mpr
    refine ⟨_, ⟨x - y, ?_, rfl⟩, u n, ⟨n, hn, rfl⟩, rfl⟩
    intro k _
    exact hxy k
  have hn₀ : n₀ ∈ F.symm '' N := ⟨_, ⟨n, hn, rfl⟩, rfl⟩
  have ha₀ : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a₀.val =
      Matrix.diagonal (fun k => Real.exp (y (σ.symm k))) := by
    change (F a₀).val = _
    rw [F.apply_symm_apply]
    rfl
  have hcore : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g₀.val =
      Matrix.diagonal (fun k => Real.exp ((x - y) k)) * (u n).val * σ.permMatrix ℝ := by
    change (F g₀).val = _
    rw [F.apply_symm_apply]
    rfl
  have hcomm := PermutationIntertwining.Construction.operatorQR_permutation_core_commutes b σ g₀ (u n).val hus
    (fun k => Real.exp ((x - y) k)) y hy hyσ hcore
  have he : PermutationSiegelPoint.Construction.permutationSiegelPoint b σ x n = g₀ * a₀ * n₀ := by
    apply F.injective
    change F (F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * P)) =
      F (F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * u n * P) *
        F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (y ∘ σ.symm)) * F.symm (P⁻¹ * v n * P))
    simp only [map_mul, F.apply_symm_apply]
    rw [hfact]
    exact PermutationDiagonalFactorization.Construction.permutation_diagonal_factorization σ (u n) (v n) hus x y hy hyσ
  rw [he]
  exact hb g₀ hg₀ n₀ hn₀ a₀ _ (fun k => Real.exp_pos _) ha₀ hcomm i j

end

/-! The permutation case of ambient translated Siegel comparison:
an output chamber bound forces a uniform output unipotent bound. -/

theorem compact_upper_permutation_siegel_comparison
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (σ : Equiv.Perm (Fin m))
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C)
    (t s : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin m → ℝ,
      (∀ i j, i.val + 1 = j.val → x i - x j ≤ t) → ∀ n ∈ C,
      (∀ i j, i.val + 1 = j.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal b (PermutationSiegelPoint.Construction.permutationSiegelPoint b σ x n) i -
          OperatorQRVal.Construction.operatorQRLogDiagonal b (PermutationSiegelPoint.Construction.permutationSiegelPoint b σ x n) j ≤ s) →
      ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b (PermutationSiegelPoint.Construction.permutationSiegelPoint b σ x n) i j| ≤ c := by
  obtain ⟨aBound, _, ha⟩ := PermutationSiegelPoint.Construction.compact_permutation_chamber_approximation b σ C hC t s ht
  obtain ⟨c, hc, hb⟩ := compact_permutation_qr_bound_of_approximation b σ C hC aBound
  refine ⟨c, hc, fun x hx n hn hg => ?_⟩
  obtain ⟨y, hy, hyσ, hxy⟩ := ha x hx n hn hg
  exact hb x n hn y hy hyσ hxy

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationApproximationQRBound.Construction
