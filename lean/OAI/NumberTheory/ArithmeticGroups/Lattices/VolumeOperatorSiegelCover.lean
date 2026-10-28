import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelOperatorRegion
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalLatticeSiegelCover
import OAI.NumberTheory.ArithmeticGroups.Lattices.CovolumeTransport

/-! # Volume Operator Siegel Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeOperatorSiegelCover.Construction

noncomputable section

/-! Integral changes of basis place every volume-preserving operator
in the inverse of the concrete ambient Siegel region. -/

open Set _root_.MeasureTheory
open scoped Classical Pointwise

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def ambientIntegralOperatorGroup {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Subgroup (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
  (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b.toBasis)
    (Submodule.span ℤ (Set.range b))).comap (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b)

theorem volume_operator_siegel_cover {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    ∃ γ ∈ ambientIntegralOperatorGroup b, (g * γ)⁻¹ ∈ Ambient.SiegelBracketFiniteness.Construction.ambientSiegelRegion b := by
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  let Λ := Submodule.span ℤ (Set.range b)
  let : DiscreteTopology Λ := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b.toBasis)))
  let : IsZLattice ℝ Λ := inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range b.toBasis)))
  obtain ⟨γ, hγ, hred⟩ := OrthonormalLatticeSiegelCover.Construction.orthonormal_lattice_standard_siegel_cover b (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g)
  have hdet : |γ.val.det| = 1 :=
    CovolumeTransport.Construction.matrix_lattice_stabilizer_abs_det_one Λ (Measure.addHaar (G := L)) b.toBasis hγ
  let δ := VolumeMatrixOperatorLift.Construction.volumeMatrixOperator b γ hdet
  have hδ : VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b δ = γ := VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom_volumeMatrixOperator b γ hdet
  refine ⟨δ, ?_, StandardSiegelOperatorRegion.Construction.standard_siegel_inverse_mem_ambient_region b (g * δ) ?_⟩
  · change VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b δ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b.toBasis) Λ
    rwa [hδ]
  · rwa [map_mul, hδ]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeOperatorSiegelCover.Construction
