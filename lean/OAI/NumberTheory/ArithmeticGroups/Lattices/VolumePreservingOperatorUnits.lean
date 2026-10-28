import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrbitMinimum
import Mathlib.Topology.Algebra.Group.Units

/-! # Volume Preserving Operator Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VolumePreservingOperatorUnits.Construction

noncomputable section

/-! The closed subgroup of continuous operator units whose determinant
has absolute value one. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

def volumePreservingOperatorUnits : Subgroup (L →L[ℝ] L)ˣ where
  carrier := {g | |g.val.toLinearMap.det| = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change |(g.val.toLinearMap.comp h.val.toLinearMap).det| = 1
    rw [LinearMap.det_comp, abs_mul, hg, hh, one_mul]
  inv_mem' {g} hg := Bracket.OrbitMinimum.Construction.abs_det_one_symm (ContinuousLinearEquiv.ofUnit g) hg

omit [FiniteDimensional ℝ L] in
theorem volumePreservingOperatorUnits_isClosed :
    IsClosed (volumePreservingOperatorUnits (L := L) : Set (L →L[ℝ] L)ˣ) :=
  isClosed_eq ((ContinuousLinearMap.continuous_det.comp Units.continuous_val).abs) continuous_const

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VolumePreservingOperatorUnits.Construction
