import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicMatrixKANBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelBracketFiniteness

/-! # Inverse Matrix Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.InverseMatrixBounds.Construction

noncomputable section

/-! The inverse ambient region used by lattice reduction has the
bounded matrix KAN coordinates required for intrinsic comparison. -/

open scoped Classical Pointwise

theorem ambient_siegel_inverse_matrix_bounds
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (hg : g ∈ (SiegelBracketFiniteness.Construction.ambientSiegelRegion b)⁻¹) :
    IntrinsicMatrixKANBounds.Construction.IsBoundedSiegelMatrix (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val.val) 1 := by
  change g⁻¹ ∈ OperatorSiegelData.Construction.ambientSiegelUnipotent b * OperatorSiegelData.Construction.ambientSiegelDiagonal b * OperatorSiegelData.Construction.ambientSiegelCompact at hg
  obtain ⟨na, hna, k, hk, he⟩ := Set.mem_mul.mp hg
  obtain ⟨n, hn, a, ha, rfl⟩ := Set.mem_mul.mp hna
  obtain ⟨d, hd, hgap, ha⟩ := ha
  have hgi : g = k⁻¹ * a⁻¹ * n⁻¹ := by
    calc
      g = (g⁻¹)⁻¹ := (inv_inv g).symm
      _ = (n * a * k)⁻¹ := by rw [← he]
      _ = k⁻¹ * a⁻¹ * n⁻¹ := by group
  let F := VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b
  refine ⟨(F k⁻¹).val, (F n⁻¹).val, d, ?_, hd, hgap, hn.1, hn.2, ?_⟩
  · exact OrthogonalOperatorMatrices.Construction.orthogonalBracketUnit_matrix b 0 (k.val⁻¹)
      ((OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup 0).inv_mem hk)
  · have hm := congrArg (fun x => (F x).val) hgi
    have ha' : (F a⁻¹).val = Matrix.diagonal d := ha
    change (F g).val = _
    simpa only [map_mul, Units.val_mul, ha'] using hm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.InverseMatrixBounds.Construction
