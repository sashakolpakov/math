import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv

/-! # Transitive Matrix Support -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TransitiveMatrixSupport.Construction

noncomputable section

/-! Transitive matrix support patterns are multiplicatively closed
and are preserved by the exponential after subtracting the identity. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorSupportSubmodule {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (r : Fin m → Fin m → Prop) : Submodule ℝ (L →L[ℝ] L) where
  carrier := {X | ∀ i j, ¬r i j → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X i j = 0}
  zero_mem' := by intro i j _; simp
  add_mem' hX hY := by intro i j h; simp [map_add, hX i j h, hY i j h]
  smul_mem' c X hX := by intro i j h; simp [hX i j h]

omit [FiniteDimensional ℝ L] in
theorem operatorSupportSubmodule_mul {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (r : Fin m → Fin m → Prop) (hr : ∀ ⦃i j k⦄, r i j → r j k → r i k)
    (X Y : L →L[ℝ] L) (hX : X ∈ operatorSupportSubmodule b r)
    (hY : Y ∈ operatorSupportSubmodule b r) : X * Y ∈ operatorSupportSubmodule b r := by
  intro i j hij
  rw [map_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : r i k
  · have hkj : ¬r k j := fun h => hij (hr hik h)
    rw [hY k j hkj, mul_zero]
  · rw [hX i k hik, zero_mul]

theorem operatorSupportSubmodule_exp_sub_one {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (r : Fin m → Fin m → Prop) (hr : ∀ ⦃i j k⦄, r i j → r j k → r i k)
    (X : L →L[ℝ] L) (hX : X ∈ operatorSupportSubmodule b r) :
    exp X - 1 ∈ operatorSupportSubmodule b r := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  exact Weight.RaisingExponential.Construction.exp_sub_one_mem_closed_multiplicative_submodule (operatorSupportSubmodule b r)
    (operatorSupportSubmodule b r).closed_of_finiteDimensional
    (fun X hX Y hY => operatorSupportSubmodule_mul b r hr X Y hX hY) X hX

omit [FiniteDimensional ℝ L] in
theorem operatorSupportSubmodule_commutes_diagonal {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ L) (r : Fin m → Fin m → Prop)
    (X : L →L[ℝ] L) (hX : X ∈ operatorSupportSubmodule b r)
    (a : Fin m → ℝ) (ha : ∀ i j, r i j → a i = a j) :
    Commute (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X) (Matrix.diagonal a) := by
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X * Matrix.diagonal a =
    Matrix.diagonal a * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : r i j
  · rw [ha i j hij, mul_comm]
  · rw [hX i j hij, zero_mul, mul_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TransitiveMatrixSupport.Construction
