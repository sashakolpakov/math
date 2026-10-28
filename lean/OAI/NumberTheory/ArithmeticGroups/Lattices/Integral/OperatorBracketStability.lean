import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeOperatorSiegelCover
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BilinearCoordinates

/-! # Operator Bracket Stability -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.OperatorBracketStability.Construction

noncomputable section

/-! Integral operator basis changes preserve integral bracket tensors. -/

open Set
open scoped Classical OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem matrixFrameAction_volumeOperator {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (x : L) :
    LatticeFrameAction.Construction.matrixFrameAction b.toBasis (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g) x = g.val.val x := by
  have he : (LatticeFrameAction.Construction.matrixFrameAction b.toBasis (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g)).toLinearMap =
      g.val.val.toLinearMap := by
    rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap]
    change Matrix.toLin b.toBasis b.toBasis
      (LinearMap.toMatrix b.toBasis b.toBasis g.val.val.toLinearMap) = _
    exact Matrix.toLin_toMatrix b.toBasis b.toBasis _
  exact LinearMap.congr_fun he x

theorem ambientIntegralOperatorGroup_maps_lattice {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (hg : g ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b)
    (x : L) (hx : x ∈ Submodule.span ℤ (Set.range b)) :
    g.val.val x ∈ Submodule.span ℤ (Set.range b) := by
  rw [← matrixFrameAction_volumeOperator b g x]
  exact ((StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (LatticeFrameAction.Construction.matrixFrameIntegralAction b.toBasis)
    (Submodule.span ℤ (Set.range b)) (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g)).mp hg x).mpr hx

theorem ambientIntegralOperatorGroup_preserves_brackets {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hg : g ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m)) :
    Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis (g • B) ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m) := by
  apply (BilinearCoordinates.Construction.integral_bilinear_coordinates_iff b.toBasis _).mpr
  intro i j
  change g.val.val (B (g.val⁻¹.val (b i)) (g.val⁻¹.val (b j))) ∈ _
  apply ambientIntegralOperatorGroup_maps_lattice b g hg
  apply BilinearCoordinates.Construction.bilinear_basis_lattice_mem b.toBasis B ((BilinearCoordinates.Construction.integral_bilinear_coordinates_iff b.toBasis B).mp hB)
  · exact ambientIntegralOperatorGroup_maps_lattice b g⁻¹ ((VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b).inv_mem hg)
      (b i) (Submodule.subset_span (Set.mem_range_self i))
  · exact ambientIntegralOperatorGroup_maps_lattice b g⁻¹ ((VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b).inv_mem hg)
      (b j) (Submodule.subset_span (Set.mem_range_self j))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.OperatorBracketStability.Construction
