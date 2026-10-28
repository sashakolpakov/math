import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MatrixSplitting
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Basis Evaluation Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationMatrices

noncomputable section

/-! Evaluating a basis gives the matrix of the evaluation map.
Injection survives arbitrary unit rescaling of its rows. -/
open scoped BigOperators
universe u v w z
variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {V : Type z} [AddCommGroup V] [Module R V]

def basisEvaluationMatrix (b : Module.Basis ν R V) (ev : V →ₗ[R] (ι → R)) : Matrix ι ν R :=
  fun i j => ev (b j) i

omit [Fintype ι] [DecidableEq ι] in
theorem basisEvaluationMatrix_linearMap (b : Module.Basis ν R V) (ev : V →ₗ[R] (ι → R)) :
    Matrix.toLin' (basisEvaluationMatrix b ev) = ev.comp b.equivFun.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, basisEvaluationMatrix]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [Fintype ι] [DecidableEq ι] in
theorem basisEvaluationMatrix_injective (b : Module.Basis ν R V) (ev : V →ₗ[R] (ι → R))
    (hev : Function.Injective ev) : Function.Injective (Matrix.toLin' (basisEvaluationMatrix b ev)) := by
  rw [basisEvaluationMatrix_linearMap]
  exact hev.comp b.equivFun.symm.injective

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_rowUnits_injective (F : Matrix ι ν R) (u : ι → Rˣ)
    (hF : Function.Injective (Matrix.toLin' F)) :
    Function.Injective (Matrix.toLin' (fun i j => (u i : R) * F i j)) := by
  intro x y hxy
  apply hF
  funext i
  apply (u i).isUnit.mul_left_cancel
  have h := congrFun hxy i
  change (∑ j, ((u i : R) * F i j) * x j) = ∑ j, ((u i : R) * F i j) * y j at h
  simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationMatrices
