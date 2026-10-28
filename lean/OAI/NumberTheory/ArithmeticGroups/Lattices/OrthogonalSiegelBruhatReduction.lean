import OAI.NumberTheory.ArithmeticGroups.Lattices.RegionFromKANFactors
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRMatrixReconstruction
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedUpperUnipotentSet
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates
import OAI.NumberTheory.ArithmeticGroups.Lattices.BruhatSiegelCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactTriangularTranslations

/-! # Orthogonal Siegel Bruhat Reduction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSiegelBruhatReduction.Construction

noncomputable section

section

/-! Ambient translated Siegel sets expressed by an orthogonal
factor, logarithmic chamber coordinates, and a compact unipotent family. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def orthogonalTranslatedSiegelSet {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (M : (Matrix (Fin m) (Fin m) ℝ)ˣ) (t : ℝ) (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) :
    Set (L →L[ℝ] L)ˣ := {g | ∃ (k : (L →L[ℝ] L)ˣ) (x : Fin m → ℝ) (n : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m),
      n ∈ C ∧ ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
      (∀ i j, i.val + 1 = j.val → x i - x j ≤ t) ∧ g = k * QRMatrixReconstruction.Construction.translatedSiegelPoint b M x n}

theorem orthogonalTranslatedSiegelSet_subset_qr_translate {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (M : (Matrix (Fin m) (Fin m) ℝ)ˣ) (t : ℝ)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ orthogonalTranslatedSiegelSet b M t C,
      ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c, g = u * (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm M := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨c, hc, hb⟩ := Compact.TriangularConjugates.Construction.compact_matrix_unit_entries_bound (Subtype.val '' C) (hC.image continuous_subtype_val)
  refine ⟨c, hc, ?_⟩
  rintro g ⟨k, x, n, hn, hk, hx, he⟩
  let a := F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x)
  have ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal (fun i => Real.exp (x i)) := by
    change (F a).val = _
    rw [F.apply_symm_apply]
    rfl
  have hN : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (F.symm n.val).val = n.val.val :=
    congrArg Units.val (F.apply_symm_apply n.val)
  have hu : k * a * F.symm n.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c := by
    apply RegionFromKANFactors.Construction.operatorQRSiegelRegion_of_factors b t c k a (F.symm n.val) _ hk
      (fun i => Real.exp_pos _) ha
    · rw [hN]
      exact n.property
    · simpa only [Real.log_exp] using hx
    · rw [hN]
      exact hb n.val ⟨n, hn, rfl⟩
  refine ⟨k * a * F.symm n.val, hu, ?_⟩
  rw [he]
  change k * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M) = (k * a * F.symm n.val) * F.symm M
  simp only [map_mul, a, mul_assoc]

theorem orthogonalTranslatedSiegelSet_of_qr_right_translate {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (x g : (L →L[ℝ] L)ˣ) (t c : ℝ)
    (hg : g ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c) :
    g * x ∈ orthogonalTranslatedSiegelSet b (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis x) t
      (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet m c) := by
  obtain ⟨k, hk, he⟩ := QRMatrixReconstruction.Construction.operatorQR_translated_reconstruction b g x
  refine ⟨k, OperatorQRVal.Construction.operatorQRLogDiagonal b g, QRMatrixReconstruction.Construction.operatorQRUpperElement b g, ?_, hk, hg.1, he⟩
  intro i j
  change |(OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val i j| ≤ c
  rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val]
  exact hg.2 i j

end

/-! Fixed ambient translates of orthogonal Siegel sets reduce to
a permutation followed by a fixed upper unipotent matrix. -/

theorem orthogonalTranslatedSiegelSet_bruhat_reduction
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (M : (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (hC : IsCompact C) (t : ℝ) (ht : 0 ≤ t) :
    ∃ (V : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m) (σ : Equiv.Perm (Fin m))
      (C' : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (t' : ℝ), IsCompact C' ∧ 0 ≤ t' ∧
      orthogonalTranslatedSiegelSet b M t C ⊆
        orthogonalTranslatedSiegelSet b (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V.val) t' C' := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨S, V, z, σ, Φ, hS, hV, hΦ, hcoord⟩ := BruhatSiegelCoordinates.Construction.matrix_bruhat_siegel_coordinates M
  refine ⟨⟨V, hV⟩, σ, Φ '' C, t + 2 * ‖z‖, hC.image hΦ,
    add_nonneg ht (mul_nonneg (by norm_num) (norm_nonneg _)), ?_⟩
  rintro g ⟨k, x, n, hn, hk, hx, he⟩
  refine ⟨k * F.symm S, x + z, Φ n, ⟨n, hn, rfl⟩, ?_, ?_, ?_⟩
  · have hSm : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (F.symm S).val = S.val :=
      congrArg Units.val (F.apply_symm_apply S)
    change (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis) (k.val * (F.symm S).val) ∈ _
    rw [map_mul, hSm]
    exact (Matrix.orthogonalGroup (Fin m) ℝ).mul_mem hk hS
  · intro i j hij
    have h₁ := hx i j hij
    have h₂ := QRCompactTriangularTranslations.Construction.finite_tuple_difference_norm_bound z i j
    change x i + z i - (x j + z j) ≤ _
    linarith
  · rw [he]
    change k * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M) =
      (k * F.symm S) * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x + z) * (Φ n).val *
        (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V))
    rw [hcoord]
    simp only [map_mul, mul_assoc]

theorem orthogonalTranslatedSiegelSet_remove_right_factor
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (M : (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m)) (t : ℝ) (h g : (L →L[ℝ] L)ˣ)
    (hg : g ∈ orthogonalTranslatedSiegelSet b (M * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis h) t C) :
    g * h⁻¹ ∈ orthogonalTranslatedSiegelSet b M t C := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  obtain ⟨k, x, n, hn, hk, hx, he⟩ := hg
  refine ⟨k, x, n, hn, hk, hx, ?_⟩
  rw [he]
  change (k * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * (M * F h))) * h⁻¹ =
    k * F.symm (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M)
  simp only [map_mul, F.symm_apply_apply]
  group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSiegelBruhatReduction.Construction
