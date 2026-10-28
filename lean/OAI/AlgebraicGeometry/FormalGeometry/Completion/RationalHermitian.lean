import OAI.AlgebraicGeometry.FormalGeometry.Completion.WeightedHermitian
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Rational Hermitian -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalHermitian.Construction

noncomputable section

/-! A positive rational diagonalization constructs a complex inner product
whose values on pure tensors recover the rational bilinear form. -/

open scoped TensorProduct BigOperators ComplexConjugate

universe u v

variable {ι : Type u} [Fintype ι] {V : Type v} [AddCommGroup V] [Module ℚ V]
  (b : Module.Basis ι ℚ V) (B : LinearMap.BilinForm ℚ V)

theorem rationalBilinear_eq_sum_diagonal (horth : B.IsOrthoᵢ b) (x y : V) :
    B x y = ∑ i, B (b i) (b i) * b.repr x i * b.repr y i := by
  classical
  calc
    B x y = ∑ i, ∑ j, b.repr x i * b.repr y j * B (b i) (b j) := by
      conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · ring
      · intro j _ hij
        rw [horth hij.symm, mul_zero]
      · simp

@[instance_reducible]
def rationalOrthogonalHermitianCore (hw : ∀ i, 0 < B (b i) (b i)) :
    InnerProductSpace.Core ℂ (TensorProduct ℚ ℂ V) :=
  WeightedHermitian.Construction.weightedHermitianCore (b.baseChange ℂ) (fun i => (B (b i) (b i) : ℝ))
    (fun i => by exact_mod_cast hw i)

theorem rationalOrthogonalHermitian_tmul (horth : B.IsOrthoᵢ b)
    (r s : ℂ) (x y : V) :
    WeightedHermitian.Construction.weightedHermitian (b.baseChange ℂ) (fun i => (B (b i) (b i) : ℝ))
      (r ⊗ₜ[ℚ] x) (s ⊗ₜ[ℚ] y) = conj r * s * (B x y : ℂ) := by
  rw [rationalBilinear_eq_sum_diagonal b B horth x y]
  simp only [WeightedHermitian.Construction.weightedHermitian, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc (a : ℚ) : algebraMap ℚ ℂ a = (a : ℂ) := rfl
  simp only [map_mul, hc, map_ratCast]
  ring

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalHermitian.Construction
