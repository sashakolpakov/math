import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Cokernel Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.CokernelCoordinates

noncomputable section

/-! Changing to basis coordinates identifies the actual cokernel of a linear
map with the cokernel of its coordinate matrix. -/

open _root_.Module

universe u v w z t
variable {R : Type u} [CommRing R]
variable {V : Type v} {W : Type w} [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
variable {ι : Type z} {κ : Type t} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem matrix_range_map_basis (bV : Basis ι R V) (bW : Basis κ R W) (f : V →ₗ[R] W) :
    (Matrix.toLin' (LinearMap.toMatrix bV bW f)).range.map bW.equivFun.symm.toLinearMap = f.range := by
  have hm : Matrix.toLin' (LinearMap.toMatrix bV bW f) =
      bW.equivFun.toLinearMap.comp (f.comp bV.equivFun.symm.toLinearMap) := by
    rw [LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix']
    rfl
  have hc : bW.equivFun.symm.toLinearMap.comp (Matrix.toLin' (LinearMap.toMatrix bV bW f)) =
      f.comp bV.equivFun.symm.toLinearMap := by
    rw [hm]
    apply LinearMap.ext
    intro x
    exact bW.equivFun.symm_apply_apply (f (bV.equivFun.symm x))
  rw [← LinearMap.range_comp, hc]
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨bV.equivFun.symm x, rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨bV.equivFun v, ?_⟩
    exact congrArg f (bV.equivFun.symm_apply_apply v)

def matrixCokernelBasisEquiv (bV : Basis ι R V) (bW : Basis κ R W) (f : V →ₗ[R] W) :
    ((κ → R) ⧸ (Matrix.toLin' (LinearMap.toMatrix bV bW f)).range) ≃ₗ[R] (W ⧸ f.range) :=
  Submodule.Quotient.equiv _ _ bW.equivFun.symm (matrix_range_map_basis bV bW f)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.CokernelCoordinates
