import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelBracketFiniteness

/-! # Standard Siegel Operator Region -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelOperatorRegion.Construction

noncomputable section

/-! The inverse of a reduced standard matrix lies in the concrete
ambient Siegel region used for integral tensor finiteness. -/

open Set
open scoped Classical Pointwise

theorem standard_siegel_inverse_mem_ambient_region
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (s : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hs : StandardSiegelMatrix.Construction.IsStandardSiegelMatrix (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b s).val) :
    s⁻¹ ∈ Ambient.SiegelBracketFiniteness.Construction.ambientSiegelRegion b := by
  obtain ⟨K, U, d, hK, hd, hstep, hupper, hdiag, hbound, hs⟩ := hs
  have hU : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U := ⟨fun {_ _} hij => hupper _ _ hij, hdiag⟩
  let kM := OrthogonalOperatorMatrices.Construction.orthogonalMatrixUnit K hK
  let uM := hU.isUnit.unit
  have huDet : |uM.val.det| = 1 := by change |U.det| = 1; rw [hU.det, abs_one]
  let k := VolumeMatrixOperatorLift.Construction.volumeMatrixOperator b kM (OrthogonalOperatorMatrices.Construction.orthogonal_matrix_abs_det K hK)
  let u := VolumeMatrixOperatorLift.Construction.volumeMatrixOperator b uM huDet
  let a := k⁻¹ * s * u⁻¹
  let F := VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b
  have hk : (F k).val = K := congrArg Units.val
    (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom_volumeMatrixOperator b kM (OrthogonalOperatorMatrices.Construction.orthogonal_matrix_abs_det K hK))
  have hu : (F u).val = U := congrArg Units.val
    (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom_volumeMatrixOperator b uM huDet)
  have hfactor : k * a * u = s := by dsimp only [a]; group
  have ha : (F a).val = Matrix.diagonal d := by
    apply kM.isUnit.mul_right_injective
    apply uM.isUnit.mul_left_injective
    change K * (F a).val * U = K * Matrix.diagonal d * U
    rw [← hk, ← hu]
    have he := congrArg (fun g => (F g).val) hfactor
    simpa only [map_mul, Units.val_mul, hk, hu] using he.trans hs
  have hkCompact : k ∈ Ambient.OperatorSiegelData.Construction.ambientSiegelCompact :=
    OrthogonalOperatorMatrices.Construction.volume_operator_of_orthogonal_matrix b k (hk ▸ hK)
  have hkInv : k⁻¹ ∈ Ambient.OperatorSiegelData.Construction.ambientSiegelCompact :=
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup (0 : L →L[ℝ] L →L[ℝ] L)).inv_mem hkCompact
  have huCompact : u ∈ Ambient.OperatorSiegelData.Construction.ambientUpperCompact b 1 := by
    change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (F u).val ∧ ∀ i j, |(F u).val i j| ≤ 1
    rw [hu]
    refine ⟨hU, fun i j => ?_⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hbound i j hij).trans (by norm_num)
    · rw [hdiag, abs_one]
    · rw [hupper i j hji, abs_zero]; norm_num
  have huInv : u⁻¹ ∈ Ambient.OperatorSiegelData.Construction.ambientSiegelUnipotent b := by
    change (u⁻¹)⁻¹ ∈ Ambient.OperatorSiegelData.Construction.ambientUpperCompact b 1
    rwa [inv_inv]
  have haInv : a⁻¹ ∈ Ambient.OperatorSiegelData.Construction.ambientSiegelDiagonal b :=
    ⟨d, hd, hstep, by simpa only [inv_inv] using ha⟩
  refine ⟨u⁻¹ * a⁻¹, ⟨u⁻¹, huInv, a⁻¹, haInv, rfl⟩, k⁻¹, hkInv, ?_⟩
  dsimp only [a]
  group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelOperatorRegion.Construction
