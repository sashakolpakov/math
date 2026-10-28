import OAI.NumberTheory.ArithmeticGroups.Lattices.QRPermutationLogFormula
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactLogBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates

/-! # Permutation Log Control -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationLogControl.Construction

noncomputable section

/-! A compact upper unipotent family gives uniform control of the
permuted input diagonal by the output QR logarithmic diagonal. -/

theorem compact_upper_permutation_log_control
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (Matrix (Fin m) (Fin m) ℝ)ˣ) (hC : IsCompact C)
    (htri : ∀ n ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular n.val)
    (t : ℝ) (ht : 0 ≤ t) (σ : Equiv.Perm (Fin m)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a : (L →L[ℝ] L)ˣ, ∀ d : Fin m → ℝ,
      (∀ i, 0 < d i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d →
      (∀ i j, i.val + 1 = j.val → Real.log (d i) - Real.log (d j) ≤ t) →
      ∀ n ∈ C, ∀ i j : Fin m,
        let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
        let g := a * F.symm n * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)
        Real.log (d (σ.symm i)) - Real.log (d (σ.symm j)) ≤
          OperatorQRVal.Construction.operatorQRLogDiagonal b g i - OperatorQRVal.Construction.operatorQRLogDiagonal b g j + R := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let P := PermutationMatrixUnits.Construction.permutationMatrixUnit σ
  obtain ⟨D, hD, hb⟩ := Compact.TriangularConjugates.Construction.compact_upper_diagonal_conjugates C hC htri
    (Real.exp ((m : ℝ) * t)) (Real.exp_pos _).le
  let Q : Set (L →L[ℝ] L)ˣ := (fun M => F.symm (M * P)) '' D
  have hQ : IsCompact Q := hD.image (F.symm.continuous.comp (continuous_id.mul continuous_const))
  obtain ⟨c, hc, hlog⟩ := QRCompactLogBounds.Construction.compact_operatorQR_log_bound b Q hQ
  refine ⟨2 * c, mul_nonneg (by norm_num) hc, fun a d hd ha hstep n hn i j => ?_⟩
  let p := F.symm P
  let n' := F.symm n
  let q := a * n' * a⁻¹ * p
  have hdD : F a * n * (F a)⁻¹ ∈ D := hb d hd
    (QRCompactLogBounds.Construction.positive_diagonal_ratio_of_log_gaps d hd t ht hstep) (F a) ha n hn
  have hq : q ∈ Q := by
    refine ⟨F a * n * (F a)⁻¹, hdD, ?_⟩
    apply F.injective
    simp only [F.apply_symm_apply, q, n', p, map_mul, map_inv]
  have hi := abs_le.mp (hlog q hq i)
  have hj := abs_le.mp (hlog q hq j)
  have hei := QRPermutationLogFormula.Construction.operatorQRLogDiagonal_permutation_formula b a n' σ d hd ha i
  have hej := QRPermutationLogFormula.Construction.operatorQRLogDiagonal_permutation_formula b a n' σ d hd ha j
  change OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n' * p) i = OperatorQRVal.Construction.operatorQRLogDiagonal b q i + _ at hei
  change OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n' * p) j = OperatorQRVal.Construction.operatorQRLogDiagonal b q j + _ at hej
  change Real.log (d (σ.symm i)) - Real.log (d (σ.symm j)) ≤
    OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n' * p) i - OperatorQRVal.Construction.operatorQRLogDiagonal b (a * n' * p) j + 2 * c
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationLogControl.Construction
