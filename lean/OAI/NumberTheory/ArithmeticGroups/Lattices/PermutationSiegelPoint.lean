import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationDiagonalFactorization
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationLogControl

/-! # Permutation Siegel Point -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationSiegelPoint.Construction

noncomputable section

/-! Ambient points in a diagonal-unipotent region translated by a
permutation, and uniform common chamber approximation of their diagonals. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def permutationSiegelPoint {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) (n : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m) :
    (L →L[ℝ] L)ˣ :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm
    (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * PermutationMatrixUnits.Construction.permutationMatrixUnit σ)

theorem compact_permutation_chamber_approximation {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (σ : Equiv.Perm (Fin m)) (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C)
    (t s : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin m → ℝ,
      (∀ i j, i.val + 1 = j.val → x i - x j ≤ t) → ∀ n ∈ C,
      (∀ i j, i.val + 1 = j.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal b (permutationSiegelPoint b σ x n) i -
          OperatorQRVal.Construction.operatorQRLogDiagonal b (permutationSiegelPoint b σ x n) j ≤ s) →
      ∃ y : Fin m → ℝ, Monotone y ∧ Monotone (y ∘ σ.symm) ∧
        ∀ i, 0 ≤ x i - y i ∧ x i - y i ≤ c := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨R, _, hR⟩ := PermutationLogControl.Construction.compact_upper_permutation_log_control b (Subtype.val '' C)
    (hC.image continuous_subtype_val) (by rintro _ ⟨n, _, rfl⟩; exact n.property) t ht σ
  let T := max t (s + R)
  obtain ⟨c, hc, hb⟩ := PermutedChamberApproximation.Construction.permuted_chamber_bounded_approximation σ.symm T (ht.trans (le_max_left _ _))
  refine ⟨c, hc, fun x hx n hn hg => ?_⟩
  let a := F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x)
  have ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal (fun i => Real.exp (x i)) := by
    change (F a).val = _
    rw [F.apply_symm_apply]
    rfl
  have hstep : ∀ i j, i.val + 1 = j.val →
      Real.log (Real.exp (x i)) - Real.log (Real.exp (x j)) ≤ t := by
    simpa only [Real.log_exp] using hx
  have he : permutationSiegelPoint b σ x n = a * F.symm n.val * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ) := by
    exact map_mul F.symm _ _ |>.trans (by rw [map_mul])
  apply hb x (fun i j hij => (hx i j hij).trans (le_max_left _ _))
  intro i j hij
  have hbound := hR a (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) ha hstep n.val
    ⟨n, hn, rfl⟩ i j
  change Real.log (Real.exp (x (σ.symm i))) - Real.log (Real.exp (x (σ.symm j))) ≤
    OperatorQRVal.Construction.operatorQRLogDiagonal b (a * F.symm n.val * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)) i -
      OperatorQRVal.Construction.operatorQRLogDiagonal b (a * F.symm n.val * F.symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)) j + R at hbound
  rw [← he, Real.log_exp, Real.log_exp] at hbound
  have hout := hg i j hij
  change x (σ.symm i) - x (σ.symm j) ≤ T
  have hT : s + R ≤ T := le_max_right _ _
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationSiegelPoint.Construction
