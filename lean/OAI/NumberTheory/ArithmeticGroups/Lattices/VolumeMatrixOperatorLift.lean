import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorCartanInvolution
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DiagonalCoordinates

/-! # Volume Matrix Operator Lift -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeMatrixOperatorLift.Construction

noncomputable section

section

/-! Closed matrix coordinates on the volume-preserving operator group,
including diagonal eigenvectors and transpose-inverse. -/

open _root_.ContinuousLinearMap
open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def volumeOperatorMatrixHom {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) →* (Matrix (Fin m) (Fin m) ℝ)ˣ :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).toMonoidHom.comp
    (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)).subtype

theorem volumeOperatorMatrixHom_val {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    (volumeOperatorMatrixHom b g).val = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val.val := rfl

theorem volumeOperatorMatrixHom_isClosedEmbedding {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Topology.IsClosedEmbedding (volumeOperatorMatrixHom b) :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).toHomeomorph.isClosedEmbedding.comp
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal

omit [FiniteDimensional ℝ L] in
theorem continuousEndMatrix_diagonal_basis {m : ℕ} (b : Module.Basis (Fin m) ℝ L)
    (A : L →L[ℝ] L) (d : Fin m → ℝ) (hA : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b A = Matrix.diagonal d)
    (i : Fin m) : A (b i) = d i • b i := by
  have he : A.toLinearMap = Matrix.toLin b b (Matrix.diagonal d) := by
    apply (LinearMap.toMatrix b b).injective
    exact hA.trans (LinearMap.toMatrix_toLin b b (Matrix.diagonal d)).symm
  change A.toLinearMap (b i) = _
  rw [he]
  exact Module.End.mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal d i b).1

theorem volumeOperatorCartanHom_matrix {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    (volumeOperatorMatrixHom b (OperatorCartanInvolution.Construction.volumeOperatorCartanHom g)).val =
      (volumeOperatorMatrixHom b g⁻¹).val.transpose := by
  ext i j
  exact OrthogonalFilteredProjection.Construction.continuousEndMatrix_adjoint_entry b (g.val⁻¹).val i j

theorem volumeOperatorCartanHom_diagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (d : Fin m → ℝ)
    (hg : (volumeOperatorMatrixHom b g⁻¹).val = Matrix.diagonal d) :
    OperatorCartanInvolution.Construction.volumeOperatorCartanHom g = g⁻¹ := by
  apply (volumeOperatorMatrixHom_isClosedEmbedding b).injective
  apply Units.ext
  rw [volumeOperatorCartanHom_matrix, hg, Matrix.diagonal_transpose]

end

/-! Every matrix of absolute determinant one lifts to the
volume-preserving operator group in a fixed orthonormal basis. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem continuousEndMatrix_det {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (A : L →L[ℝ] L) :
    (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b A).det = A.toLinearMap.det := LinearMap.det_toMatrix b A.toLinearMap

def volumeMatrixOperator {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (Matrix (Fin m) (Fin m) ℝ)ˣ) (hg : |g.val.det| = 1) :
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) := by
  let u := (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm g
  refine ⟨u, ?_⟩
  have he : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis u.val = g.val :=
    congrArg Units.val ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).apply_symm_apply g)
  change |u.val.toLinearMap.det| = 1
  rw [← continuousEndMatrix_det b.toBasis u.val, he]
  exact hg

theorem volumeOperatorMatrixHom_volumeMatrixOperator {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (g : (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (hg : |g.val.det| = 1) : volumeOperatorMatrixHom b (volumeMatrixOperator b g hg) = g :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).apply_symm_apply g

theorem volumeOperatorMatrixHom_abs_det {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) : |(volumeOperatorMatrixHom b g).val.det| = 1 := by
  rw [volumeOperatorMatrixHom_val, continuousEndMatrix_det]
  exact g.property

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeMatrixOperatorLift.Construction
