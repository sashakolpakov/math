import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Group.Units

/-! # Filtered Matrix Unit Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredMatrixUnitProjection.Construction

noncomputable section

/-! Filter-preserving invertible matrices form a closed group, and
their diagonal-block projection is a continuous group homomorphism. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightFilteredMatrixUnits (w : ι → ℝ) : Subgroup (Matrix ι ι ℝ)ˣ :=
  (Matrix.blockTriangularSubalgebra (α := OrderDual ℝ) ℝ ℝ w).toSubmonoid.units

theorem weightFilteredMatrixUnits_isClosed (w : ι → ℝ) :
    IsClosed (weightFilteredMatrixUnits w : Set (Matrix ι ι ℝ)ˣ) := by
  have hS : IsClosed (Matrix.blockTriangularSubalgebra (α := OrderDual ℝ) ℝ ℝ w : Set (Matrix ι ι ℝ)) :=
    (Matrix.blockTriangularSubalgebra (α := OrderDual ℝ) ℝ ℝ w).toSubmodule.closed_of_finiteDimensional
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

def weightBlockUnitProjection (w : ι → ℝ) : weightFilteredMatrixUnits w →* (Matrix ι ι ℝ)ˣ where
  toFun g := {
    val := Weight.BlockProjection.Construction.weightBlockProjection w (g.val : Matrix ι ι ℝ)
    inv := Weight.BlockProjection.Construction.weightBlockProjection w (↑g.val⁻¹ : Matrix ι ι ℝ)
    val_inv := by
      rw [← Weight.BlockProjection.Construction.weightBlockProjection_mul w (g.val : Matrix ι ι ℝ) (↑g.val⁻¹ : Matrix ι ι ℝ)
        g.property.1 g.property.2, Units.mul_inv, Weight.BlockProjection.Construction.weightBlockProjection_one]
    inv_val := by
      rw [← Weight.BlockProjection.Construction.weightBlockProjection_mul w (↑g.val⁻¹ : Matrix ι ι ℝ) (g.val : Matrix ι ι ℝ)
        g.property.2 g.property.1, Units.inv_mul, Weight.BlockProjection.Construction.weightBlockProjection_one] }
  map_one' := by
    apply Units.ext
    exact Weight.BlockProjection.Construction.weightBlockProjection_one w
  map_mul' g h := by
    apply Units.ext
    exact Weight.BlockProjection.Construction.weightBlockProjection_mul w _ _ g.property.1 h.property.1

theorem weightBlockUnitProjection_val (w : ι → ℝ) (g : weightFilteredMatrixUnits w) :
    (weightBlockUnitProjection w g : Matrix ι ι ℝ) = Weight.BlockProjection.Construction.weightBlockProjection w (g.val : Matrix ι ι ℝ) := rfl

theorem weightBlockUnitProjection_continuous (w : ι → ℝ) : Continuous (weightBlockUnitProjection w) := by
  have hP : Continuous (Weight.BlockProjection.Construction.weightBlockProjection (R := ℝ) w) :=
    (Weight.BlockProjection.Construction.weightBlockProjection (R := ℝ) w).continuous_of_finiteDimensional
  apply Units.continuous_iff.mpr
  exact ⟨hP.comp (Units.continuous_val.comp continuous_subtype_val),
    hP.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredMatrixUnitProjection.Construction
