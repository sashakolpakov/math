import OAI.NumberTheory.ArithmeticGroups.Lattices.BruhatSiegelCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationApproximationQRBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactTriangularTranslations

/-! # QR Matrix Reconstruction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRMatrixReconstruction.Construction

noncomputable section

section

/-! Ambient translated Siegel comparison: for any fixed real
invertible matrix, an output chamber bound controls the output
unipotent coordinates uniformly. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def translatedSiegelPoint {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (M : (Matrix (Fin m) (Fin m) ℝ)ˣ) (x : Fin m → ℝ) (n : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m) :
    (L →L[ℝ] L)ˣ :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M)

theorem compact_upper_translated_siegel_comparison {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (M : (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C)
    (t s : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin m → ℝ,
      (∀ i j, i.val + 1 = j.val → x i - x j ≤ t) → ∀ n ∈ C,
      (∀ i j, i.val + 1 = j.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal b (translatedSiegelPoint b M x n) i -
          OperatorQRVal.Construction.operatorQRLogDiagonal b (translatedSiegelPoint b M x n) j ≤ s) →
      ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b (translatedSiegelPoint b M x n) i j| ≤ c := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨S, V, z, σ, Φ, hS, hV, hΦ, hcoord⟩ := BruhatSiegelCoordinates.Construction.matrix_bruhat_siegel_coordinates M
  let T := t + 2 * ‖z‖
  have hT : 0 ≤ T := add_nonneg ht (mul_nonneg (by norm_num) (norm_nonneg _))
  obtain ⟨c₀, _, hb⟩ := PermutationApproximationQRBound.Construction.compact_upper_permutation_siegel_comparison b σ (Φ '' C) (hC.image hΦ) T s hT
  let D : Set (Matrix (Fin m) (Fin m) ℝ)ˣ :=
    {u | UpperUnitriangularMatrices.Construction.IsUpperUnitriangular u.val ∧ ∀ i j, |u.val i j| ≤ c₀}
  have hD : IsCompact D := UpperUnitriangularMatrices.Construction.bounded_upper_unitriangular_isCompact m c₀
  obtain ⟨c, hc, hbound⟩ := Compact.TriangularConjugates.Construction.compact_matrix_unit_entries_bound ((fun u => u * V) '' D)
    (hD.image (continuous_id.mul continuous_const))
  refine ⟨c, hc, fun x hx n hn hg i j => ?_⟩
  let g₀ := PermutationSiegelPoint.Construction.permutationSiegelPoint b σ (x + z) (Φ n)
  have hS' : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (F.symm S).val ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    change (F (F.symm S)).val ∈ _
    rw [F.apply_symm_apply]
    exact hS
  have hV' : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (F.symm V).val) := by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (F (F.symm V)).val
    rw [F.apply_symm_apply]
    exact hV
  have he : translatedSiegelPoint b M x n = F.symm S * g₀ * F.symm V := by
    apply F.injective
    change F (F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M)) =
      F (F.symm S * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x + z) * (Φ n).val * PermutationMatrixUnits.Construction.permutationMatrixUnit σ) * F.symm V)
    simp only [map_mul, F.apply_symm_apply]
    rw [hcoord]
    simp only [mul_assoc]
  have hqr := QRCompactTriangularTranslations.Construction.operatorQR_orthogonal_unipotent_coordinates b (F.symm S) g₀ (F.symm V) hS' hV'
  have hlog : OperatorQRVal.Construction.operatorQRLogDiagonal b (translatedSiegelPoint b M x n) = OperatorQRVal.Construction.operatorQRLogDiagonal b g₀ := by
    rw [he]
    exact hqr.1
  have hx' : ∀ i j, i.val + 1 = j.val → (x + z) i - (x + z) j ≤ T := by
    intro i j hij
    have hh := hx i j hij
    have hz := QRCompactTriangularTranslations.Construction.finite_tuple_difference_norm_bound z i j
    change x i + z i - (x j + z j) ≤ t + 2 * ‖z‖
    linarith
  have hg₀ : ∀ i j, i.val + 1 = j.val →
      OperatorQRVal.Construction.operatorQRLogDiagonal b g₀ i - OperatorQRVal.Construction.operatorQRLogDiagonal b g₀ j ≤ s := by
    intro i j hij
    rw [← hlog]
    exact hg i j hij
  have hUb := hb (x + z) hx' (Φ n) ⟨n, hn, rfl⟩ hg₀
  have hUD : OperatorQRVal.Construction.operatorQRUnipotentUnit b g₀ ∈ D := by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (OperatorQRVal.Construction.operatorQRUnipotentUnit b g₀).val ∧ _
    simp only [OperatorQRVal.Construction.operatorQRUnipotentUnit_val]
    exact ⟨OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g₀, hUb⟩
  have hU : OperatorQRVal.Construction.operatorQRUnipotentUnit b (translatedSiegelPoint b M x n) = OperatorQRVal.Construction.operatorQRUnipotentUnit b g₀ * V := by
    rw [he, hqr.2]
    change OperatorQRVal.Construction.operatorQRUnipotentUnit b g₀ * F (F.symm V) = _
    rw [F.apply_symm_apply]
  have hmem : OperatorQRVal.Construction.operatorQRUnipotentUnit b (translatedSiegelPoint b M x n) ∈ (fun u => u * V) '' D :=
    ⟨OperatorQRVal.Construction.operatorQRUnipotentUnit b g₀, hUD, hU.symm⟩
  simpa only [OperatorQRVal.Construction.operatorQRUnipotentUnit_val] using hbound _ hmem i j

end

/-! Reconstructing an arbitrary operator from its ambient QR
coordinates, also after right multiplication by a fixed operator. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorQRUpperElement {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m :=
  ⟨OperatorQRVal.Construction.operatorQRUnipotentUnit b g, by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val
    rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val]
    exact OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g⟩

theorem operatorQR_translated_reconstruction {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g x : (L →L[ℝ] L)ˣ) :
    ∃ k : (L →L[ℝ] L)ˣ,
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
      g * x = k * translatedSiegelPoint b (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis x)
        (OperatorQRVal.Construction.operatorQRLogDiagonal b g) (operatorQRUpperElement b g) := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let K := OrthogonalOperatorMatrices.Construction.orthogonalMatrixUnit (OperatorQRVal.Construction.operatorQRCompactMatrix b g) (OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g)
  let k := F.symm K
  have hFk : F k = K := F.apply_symm_apply _
  have hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    change (F k).val ∈ _
    rw [F.apply_symm_apply]
    exact OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g
  refine ⟨k, hk, ?_⟩
  apply F.injective
  change F (g * x) = F (k * F.symm
    (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (OperatorQRVal.Construction.operatorQRLogDiagonal b g) * (operatorQRUpperElement b g).val * F x))
  simp only [map_mul, F.apply_symm_apply, hFk]
  apply Units.ext
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val * (F x).val =
    OperatorQRVal.Construction.operatorQRCompactMatrix b g *
      (Matrix.diagonal (fun i => Real.exp (OperatorQRVal.Construction.operatorQRLogDiagonal b g i)) *
        (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val * (F x).val)
  have he : (fun i => Real.exp (OperatorQRVal.Construction.operatorQRLogDiagonal b g i)) = OperatorQRBasis.Construction.operatorQRDiagonal b g := by
    funext i
    exact Real.exp_log (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i)
  rw [he, OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQR_kan_factorization b g]
  simp only [mul_assoc]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRMatrixReconstruction.Construction
