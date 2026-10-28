import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockKernel
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedTriangularCompatibility

/-! # Positive Block Kernel Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PositiveBlockKernelEquiv.Construction

noncomputable section

/-! In an ordered orthonormal basis, the positive operator group is
continuously isomorphic to the kernel of equal-weight block projection. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def orderedPositiveBlockKernelHom {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) :
    UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w →* (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw).ker where
  toFun g := ⟨⟨ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis g.val,
    OrderedTriangularCompatibility.Construction.ordered_weightRaising_unitriangular b w hw g.val g.property⟩, by
      apply (UpperUnipotentBlockKernel.Construction.upperUnitriangularBlockProjection_kernel_iff w hw _).mpr
      intro i j hij
      change (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val.val - 1) i j = 0
      have h := (OperatorWeightMatrix.Construction.weightRaising_matrix_iff b w (g.val.val - 1)).mp g.property i j hij
      simpa only [map_sub, map_one] using h⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).map_mul g.val h.val

def orderedPositiveBlockKernelInv {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) :
    (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw).ker → UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w :=
  fun h => ⟨(ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm h.val.val, by
    apply (OperatorWeightMatrix.Construction.weightRaising_matrix_iff b w _).mpr
    intro i j hij
    rw [map_sub, map_one]
    have hm : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis
        ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm h.val.val).val = h.val.val.val :=
      congrArg Units.val ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).apply_symm_apply h.val.val)
    rw [hm]
    exact (UpperUnipotentBlockKernel.Construction.upperUnitriangularBlockProjection_kernel_iff w hw h.val).mp h.property i j hij⟩

def orderedPositiveBlockKernelEquiv {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) :
    UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w ≃ₜ* (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hw).ker where
  toFun := orderedPositiveBlockKernelHom b w hw
  invFun := orderedPositiveBlockKernelInv b w hw
  left_inv g := by
    apply Subtype.ext
    exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm_apply_apply g.val
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).apply_symm_apply h.val.val
  map_mul' := (orderedPositiveBlockKernelHom b w hw).map_mul
  continuous_toFun :=
    (((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PositiveBlockKernelEquiv.Construction
