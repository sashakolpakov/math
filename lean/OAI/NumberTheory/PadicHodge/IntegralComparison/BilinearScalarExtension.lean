import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Bilinear Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

noncomputable section

/-! Scalar extension of a native bilinear map, with its pure-tensor,
naturality and unit formulas. -/

open scoped TensorProduct

universe u v w x y z

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {M : Type w} {N : Type x} {P : Type y}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def map (μ : M →ₗ[R] N →ₗ[R] P) :
    S ⊗[R] M →ₗ[S] S ⊗[R] N →ₗ[S] S ⊗[R] P :=
  TensorProduct.curry (((TensorProduct.lift μ).baseChange S).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).symm.toLinearMap)

theorem map_tmul (μ : M →ₗ[R] N →ₗ[R] P) (a b : S) (x : M) (y : N) :
    map S μ (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) = (a * b) ⊗ₜ[R] μ x y := by
  change (TensorProduct.lift μ).baseChange S
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).symm
      ((a ⊗ₜ[R] x) ⊗ₜ[S] (b ⊗ₜ[R] y))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, TensorProduct.lift.tmul]

variable {M' : Type w} {N' : Type x} {P' : Type z}
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  [AddCommGroup P'] [Module R P']

theorem map_natural (μ : M →ₗ[R] N →ₗ[R] P) (ν : M' →ₗ[R] N' →ₗ[R] P')
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (hμ : ∀ x y, h (μ x y) = ν (f x) (g y))
    (x : S ⊗[R] M) (y : S ⊗[R] N) :
    h.baseChange S (map S μ x y) = map S ν (f.baseChange S x) (g.baseChange S y) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b y => simp only [map_tmul, LinearMap.baseChange_tmul, hμ]

theorem map_right_unit (μ : M →ₗ[R] N →ₗ[R] M) (e : N)
    (he : ∀ x, μ x e = x) (x : S ⊗[R] M) :
    map S μ x ((1 : S) ⊗ₜ[R] e) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a x => rw [map_tmul, he, mul_one]

theorem map_left_unit (μ : M →ₗ[R] N →ₗ[R] N) (e : M)
    (he : ∀ y, μ e y = y) (y : S ⊗[R] N) :
    map S μ ((1 : S) ⊗ₜ[R] e) y = y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b y => rw [map_tmul, he, one_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension
