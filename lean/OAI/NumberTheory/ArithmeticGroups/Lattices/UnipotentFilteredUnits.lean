import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Unipotent Filtered Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentFilteredUnits.Construction

noncomputable section

/-! Weight-unipotent operators preserve the filtration and have
identity diagonal-block projection. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem weightRaising_sub_one_matrix_entry {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (A : L →L[ℝ] L)
    (hA : A - 1 ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) (i j : Fin m) (hij : w i ≤ w j) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j = 0 := by
  have h := (OperatorWeightMatrix.Construction.weightRaising_matrix_iff b w (A - 1)).mp hA i j hij
  simpa only [map_sub, map_one, Matrix.sub_apply] using h

omit [FiniteDimensional ℝ L] in
theorem weightRaising_sub_one_matrix_filtered {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (A : L →L[ℝ] L)
    (hA : A - 1 ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    Matrix.BlockTriangular (α := OrderDual ℝ) (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A) w := by
  intro i j hij
  have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
  have h := weightRaising_sub_one_matrix_entry b w A hA i j (le_of_lt hij)
  rwa [Matrix.one_apply_ne hne, sub_zero] at h

omit [FiniteDimensional ℝ L] in
theorem weightRaising_sub_one_blockProjection {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) (A : L →L[ℝ] L)
    (hA : A - 1 ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    Weight.BlockProjection.Construction.weightBlockProjection w (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A) = 1 := by
  ext i j
  rw [Weight.BlockProjection.Construction.weightBlockProjection_apply]
  by_cases hij : w i = w j
  · rw [ite_eq_left hij]
    exact sub_eq_zero.mp (weightRaising_sub_one_matrix_entry b w A hA i j hij.le)
  · have hne : i ≠ j := fun h => hij (congrArg w h)
    rw [ite_eq_right hij, Matrix.one_apply_ne hne]

theorem weightRaisingUnitGroup_le_filtered {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ) :
    UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w ≤ FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w := by
  intro g hg
  have hi := (UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w).inv_mem hg
  constructor
  · change Matrix.BlockTriangular (α := OrderDual ℝ)
      (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g : L →L[ℝ] L)) w
    exact weightRaising_sub_one_matrix_filtered b w _ hg
  · change Matrix.BlockTriangular (α := OrderDual ℝ)
      ((↑((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis g)⁻¹)) : Matrix (Fin m) (Fin m) ℝ) w
    rw [← map_inv, ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv_val]
    exact weightRaising_sub_one_matrix_filtered b w _ hi

theorem weightRaising_unit_blockProjection_eq_one {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (g : FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w) (hg : g.val ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w) :
    FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w g = 1 := by
  apply Units.ext
  apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrix_bijective b.toBasis).1
  rw [Units.val_one, map_one]
  exact (FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection_matrix b.toBasis w g).trans
    (weightRaising_sub_one_blockProjection b w (g.val : L →L[ℝ] L) hg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentFilteredUnits.Construction
