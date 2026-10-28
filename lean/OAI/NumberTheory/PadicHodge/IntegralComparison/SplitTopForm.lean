import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Split Top Form -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SplitTopForm

noncomputable section

/-! The determinant form of a split exact sequence is independent of
its splitting. This gives the orientation compatibility needed for the
conormal description of the canonical module. -/

open _root_.Module

universe u v w t

variable {R : Type u} [CommRing R]
  {U : Type v} [AddCommGroup U] [Module R U]
  {W : Type w} [AddCommGroup W] [Module R W]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (bU : Basis ι R U) (bW : Basis κ R W)

include bU bW in
theorem det_eq_mul (T : (U × W) →ₗ[R] U × W) (a : U →ₗ[R] U) (d : W →ₗ[R] W)
    (hU : ∀ u, T (u, 0) = (a u, 0)) (hW : ∀ z, (T z).2 = d z.2) :
    T.det = a.det * d.det := by
  let B : Matrix ι κ R := fun i j => bU.repr (T (0, bW j)).1 i
  have hT : LinearMap.toMatrix (bU.prod bW) (bU.prod bW) T =
      Matrix.fromBlocks (LinearMap.toMatrix bU bU a) B 0 (LinearMap.toMatrix bW bW d) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hU]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, B, Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hU]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hW]
  rw [← LinearMap.det_toMatrix (bU.prod bW), hT, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

include bU bW in
theorem det_eq_one (T : (U × W) →ₗ[R] U × W)
    (hU : ∀ u, T (u, 0) = (u, 0)) (hW : ∀ z, (T z).2 = z.2) : T.det = 1 := by
  simpa using det_eq_mul bU bW T LinearMap.id LinearMap.id hU hW

variable {V : Type t} [AddCommGroup V] [Module R V]

theorem topForm_eq (e f : (U × W) ≃ₗ[R] V)
    (hU : ∀ u, e (u, 0) = f (u, 0))
    (hW : ∀ v, (e.symm v).2 = (f.symm v).2) :
    ((bU.prod bW).map e).det = ((bU.prod bW).map f).det := by
  classical
  let T : (U × W) →ₗ[R] U × W := (f.trans e.symm).toLinearMap
  have hTU (u : U) : T (u, 0) = (u, 0) := by
    change e.symm (f (u, 0)) = _
    rw [← hU, e.symm_apply_apply]
  have hTW (z : U × W) : (T z).2 = z.2 := by
    change (e.symm (f z)).2 = z.2
    rw [hW, f.symm_apply_apply]
  have hdet := det_eq_one bU bW T hTU hTW
  have hvalue : ((bU.prod bW).map e).det ((bU.prod bW).map f) = 1 := by
    rw [Basis.det_map]
    change (bU.prod bW).det (T ∘ (bU.prod bW)) = 1
    rw [Basis.det_comp, hdet, Basis.det_self, one_mul]
  rw [(((bU.prod bW).map e).det).eq_smul_basis_det ((bU.prod bW).map f), hvalue, one_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SplitTopForm
