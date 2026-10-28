import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness

/-! # Orthogonal Symmetric Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSymmetricExponential.Construction

noncomputable section

/-! The only orthogonal exponential of a real symmetric operator
is the identity, and its symmetric logarithm is zero. -/

open NormedSpace

theorem symmetric_exponential_orthogonal_eq_zero
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric)
    (horth : ∀ x y, inner ℝ (exp A x) (exp A y) = inner ℝ x y) : A = 0 := by
  let b := hA.eigenvectorBasis rfl
  let w := hA.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ L)) : A (b i) = w i • b i := hA.apply_eigenvectorBasis rfl i
  have hw (i : Fin (Module.finrank ℝ L)) : w i = 0 := by
    have he : exp A (b i) = Real.exp (w i) • b i := SpectralOperatorExponential.Construction.exp_apply_eigenbasis b.toBasis w A heig i
    have h := horth (b i) (b i)
    rw [he] at h
    simp only [real_inner_smul_left, real_inner_smul_right, b.inner_eq_ite, ite_true, mul_one] at h
    have he₁ : Real.exp (w i) = 1 := by nlinarith [Real.exp_pos (w i)]
    exact Real.exp_injective (he₁.trans Real.exp_zero.symm)
  have hz : A.toLinearMap = 0 := by
    apply b.toBasis.ext
    intro i
    change A (b i) = 0
    rw [heig, hw, zero_smul]
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun hz x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSymmetricExponential.Construction
