import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFunctor

/-! # Diagonal Tensor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor

noncomputable section

/-! Restricting the external tensor product to the actual diagonal
recovers the ordinary tensor product over the original ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]

abbrev Ring := R ⊗[K] R

abbrev multiplication : Ring K R →+* R := (Algebra.TensorProduct.lmul' K (S := R)).toRingHom

abbrev diagonalAlgebra : Algebra (Ring K R) R := (multiplication K R).toAlgebra

attribute [local instance] diagonalAlgebra
  ExternalTensorFunctor.scalar ExternalTensorFunctor.tower ExternalTensor.module

variable (M N : ModuleCat.{u} R)

def contraction : ExternalTensor.obj K R R M N ⟶
    (ModuleCat.restrictScalars (multiplication K R)).obj (.of R (M ⊗[R] N)) := by
  let f : M ⊗[K] N →ₗ[K] M ⊗[R] N :=
    TensorProduct.lift ((TensorProduct.mk R M N).restrictScalars₁₂ K K)
  exact ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (multiplication K R)).obj (.of R (M ⊗[R] N)))
    { f with
      map_smul' := by
        intro a x
        change f (a • x) = (multiplication K R a) • f x
        induction a using TensorProduct.inductionOn with
        | tmul r s =>
          induction x using TensorProduct.inductionOn with
          | tmul m n =>
            change (r • m) ⊗ₜ[R] (s • n) = (r * s) • (m ⊗ₜ[R] n)
            exact TensorProduct.smul_tmul_smul r s m n
          | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | add a b ha hb => simp only [add_smul, map_add, ha, hb] }

theorem contraction_tmul (m : M) (n : N) :
    contraction K R M N (m ⊗ₜ[K] n) = m ⊗ₜ[R] n := rfl

def extended : R ⊗[Ring K R] ExternalTensor.obj K R R M N →ₗ[R] M ⊗[R] N := by
  let := Module.restrictScalars (Ring K R) R (M ⊗[R] N)
  let := IsScalarTower.restrictScalars (Ring K R) R (M ⊗[R] N)
  exact LinearMap.liftBaseChange R (contraction K R M N).hom

theorem extended_tmul (r : R) (m : M) (n : N) :
    extended K R M N (r ⊗ₜ[Ring K R] (m ⊗ₜ[K] n)) = r • (m ⊗ₜ[R] n) := rfl

theorem left_balance (r : R) (m : M) (n : N) :
    (1 : R) ⊗ₜ[Ring K R] ((r • m) ⊗ₜ[K] n : ExternalTensor.obj K R R M N) =
      r • ((1 : R) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)) := by
  have h := TensorProduct.tmul_smul (R := Ring K R) (r ⊗ₜ[K] (1 : R)) (1 : R)
    (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)
  calc
    _ = (r ⊗ₜ[K] (1 : R)) • ((1 : R) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)) := by
      simpa only [ExternalTensor.smul_tmul, one_smul] using h
    _ = _ := by
      simp only [TensorProduct.smul_tmul']
      change ((r * 1) * 1) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n) = (r * 1) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n)
      simp only [mul_one]

theorem right_balance (r : R) (m : M) (n : N) :
    (1 : R) ⊗ₜ[Ring K R] (m ⊗ₜ[K] (r • n) : ExternalTensor.obj K R R M N) =
      r • ((1 : R) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)) := by
  have h := TensorProduct.tmul_smul (R := Ring K R) ((1 : R) ⊗ₜ[K] r) (1 : R)
    (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)
  calc
    _ = ((1 : R) ⊗ₜ[K] r) • ((1 : R) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n : ExternalTensor.obj K R R M N)) := by
      simpa only [ExternalTensor.smul_tmul, one_smul] using h
    _ = _ := by
      simp only [TensorProduct.smul_tmul']
      change ((1 * r) * 1) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n) = (r * 1) ⊗ₜ[Ring K R] (m ⊗ₜ[K] n)
      simp only [one_mul]

def inverseBilinear : M →ₗ[R] N →ₗ[R]
    R ⊗[Ring K R] ExternalTensor.obj K R R M N where
  toFun m :=
    { toFun := fun n => 1 ⊗ₜ[Ring K R] (m ⊗ₜ[K] n)
      map_add' := by intro n n'; simp only [TensorProduct.tmul_add]
      map_smul' := by intro r n; exact right_balance K R M N r m n }
  map_add' := by
    intro m m'
    apply LinearMap.ext
    intro n
    change (1 : R) ⊗ₜ[Ring K R] ((m + m') ⊗ₜ[K] n) =
      1 ⊗ₜ[Ring K R] (m ⊗ₜ[K] n) + 1 ⊗ₜ[Ring K R] (m' ⊗ₜ[K] n)
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  map_smul' := by intro r m; ext n; exact left_balance K R M N r m n

def inverse : M ⊗[R] N →ₗ[R] R ⊗[Ring K R] ExternalTensor.obj K R R M N :=
  TensorProduct.lift (inverseBilinear K R M N)

theorem inverse_tmul (m : M) (n : N) :
    inverse K R M N (m ⊗ₜ[R] n) = 1 ⊗ₜ[Ring K R] (m ⊗ₜ[K] n) := rfl

def equiv : R ⊗[Ring K R] ExternalTensor.obj K R R M N ≃ₗ[R] M ⊗[R] N :=
  { extended K R M N with
    invFun := inverse K R M N
    left_inv := by
      intro x
      change inverse K R M N (extended K R M N x) = x
      induction x using TensorProduct.inductionOn with
      | tmul r x =>
        induction x using TensorProduct.inductionOn with
        | tmul m n =>
          rw [extended_tmul, map_smul, inverse_tmul, TensorProduct.smul_tmul']
          simp only [smul_eq_mul, mul_one]
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    right_inv := by
      intro x
      change extended K R M N (inverse K R M N x) = x
      induction x using TensorProduct.inductionOn with
      | tmul m n => rw [inverse_tmul, extended_tmul, one_smul]
      | add x y hx hy => simp only [map_add, hx, hy] }

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor
