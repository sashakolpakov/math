import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumePreservingOperatorUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalFilteredProjection

/-! # Operator Cartan Involution -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorCartanInvolution.Construction

noncomputable section

/-! Transpose-inverse is a continuous involutive automorphism of the
volume-preserving real operator group. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuous_operator_adjoint_det (A : L →L[ℝ] L) :
    (adjoint A).toLinearMap.det = A.toLinearMap.det := by
  let b := stdOrthonormalBasis ℝ L
  have he : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (adjoint A) =
      (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A).transpose := by
    ext i j
    exact OrthogonalFilteredProjection.Construction.continuousEndMatrix_adjoint_entry b A i j
  have hd := congrArg Matrix.det he
  rw [Matrix.det_transpose] at hd
  change (LinearMap.toMatrix b.toBasis b.toBasis (adjoint A).toLinearMap).det =
    (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).det at hd
  simpa only [LinearMap.det_toMatrix] using hd

def operatorCartanHom : (L →L[ℝ] L)ˣ →* (L →L[ℝ] L)ˣ := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  exact {
    toFun := fun g => star g⁻¹
    map_one' := by simp
    map_mul' := by intros; simp }

theorem operatorCartanHom_val (g : (L →L[ℝ] L)ˣ) :
    (operatorCartanHom g).val = adjoint (g⁻¹).val := rfl

theorem operatorCartanHom_continuous : Continuous (operatorCartanHom (L := L)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact adjoint.continuous.comp (Units.continuous_val.comp continuous_inv)
  · exact adjoint.continuous.comp Units.continuous_val

theorem operatorCartanHom_involutive : Function.Involutive (operatorCartanHom (L := L)) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  intro g
  change star (star g⁻¹)⁻¹ = g
  simp

theorem operatorCartanHom_preserves_volume (g : (L →L[ℝ] L)ˣ)
    (hg : g ∈ VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits) :
    operatorCartanHom g ∈ VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits := by
  change |(adjoint (g⁻¹).val).toLinearMap.det| = 1
  rw [continuous_operator_adjoint_det]
  exact (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)).inv_mem hg

def volumeOperatorCartanHom : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) →*
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) :=
  (operatorCartanHom.comp (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)).subtype).codRestrict
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (fun g => operatorCartanHom_preserves_volume g.val g.property)

theorem volumeOperatorCartanHom_continuous :
    Continuous (volumeOperatorCartanHom (L := L)) :=
  (operatorCartanHom_continuous.comp continuous_subtype_val).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorCartanInvolution.Construction
