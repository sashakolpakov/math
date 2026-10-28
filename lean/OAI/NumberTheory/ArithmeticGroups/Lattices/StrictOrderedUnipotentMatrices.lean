import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Strict Ordered Unipotent Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StrictOrderedUnipotentMatrices.Construction

noncomputable section

/-! Strictly decreasing weights identify the weight-raising
unipotent operators with the full upper unitriangular matrix group. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem weightRaising_unit_matrix_upper {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) (g : UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val.val) := by
  have hg : ∀ i j, w i ≤ w j →
      (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val.val - 1) i j = 0 := by
    intro i j hij
    have he := g.property i j hij
    simpa only [← OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply, map_sub, map_one] using he
  constructor
  · intro i j hij
    change j < i at hij
    have he := hg i j (hw hij.le)
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), sub_zero] using he
  · intro i
    have he := hg i i le_rfl
    simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] using he

omit [FiniteDimensional ℝ L] in
theorem upper_matrix_unit_weightRaising {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : StrictAnti w) (g : (L →L[ℝ] L)ˣ)
    (hg : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val)) :
    g ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w := by
  intro i j hij
  rw [← OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply, map_sub, map_one, Matrix.sub_apply]
  have hji : j ≤ i := by
    by_contra hn
    exact (not_lt_of_ge hij) (hw (lt_of_not_ge hn))
  rcases hji.eq_or_lt with he | he
  · subst j
    rw [hg.2 i, Matrix.one_apply_eq, sub_self]
  · rw [hg.1 he, Matrix.one_apply_ne (ne_of_gt he), sub_self]

def strictOrderedUnipotentMatrixEquiv {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : StrictAnti w) :
    UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w ≃ₜ* UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m where
  toFun g := ⟨ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis g.val,
    weightRaising_unit_matrix_upper b w hw.antitone g⟩
  invFun g := ⟨(ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm g.val,
    upper_matrix_unit_weightRaising b w hw _ (by
      change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular
        ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
          ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm g.val)).val)
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact g.property)⟩
  left_inv g := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm_apply_apply g.val
  right_inv g := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).apply_symm_apply g.val
  map_mul' g h := by apply Subtype.ext; exact map_mul (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis) g.val h.val
  continuous_toFun := ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis).symm.continuous.comp continuous_subtype_val).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StrictOrderedUnipotentMatrices.Construction
