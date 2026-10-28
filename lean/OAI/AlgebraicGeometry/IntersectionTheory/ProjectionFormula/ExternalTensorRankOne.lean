import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFunctor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OneSidedTor

/-! # External Tensor Rank One -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorRankOne

noncomputable section

/-! The external tensor product of the rank-one module with N is the
native extension of N along the second product factor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (K R S : Type u) [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  ExternalTensorFunctor.scalar ExternalTensorFunctor.tower ExternalTensor.module

variable (N : ModuleCat.{u} S)

abbrev target : ModuleCat.{u} (R ⊗[K] S) := ExternalTensor.obj K R S R N

local instance : Module S (target K R S N) := Module.restrictScalars S (R ⊗[K] S) (target K R S N)
local instance : IsScalarTower S (R ⊗[K] S) (target K R S N) :=
  IsScalarTower.restrictScalars S (R ⊗[K] S) (target K R S N)

def unitLinear : N →ₗ[S] target K R S N where
  toFun n := (1 : R) ⊗ₜ[K] n
  map_add' := TensorProduct.tmul_add 1
  map_smul' := by
    intro s n
    change (1 : R) ⊗ₜ[K] (s • n) = ((1 : R) ⊗ₜ[K] s) • ((1 : R) ⊗ₜ[K] n : target K R S N)
    rw [ExternalTensor.smul_tmul]
    rw [one_smul]

def forward : (R ⊗[K] S) ⊗[S] N →ₗ[R ⊗[K] S] target K R S N :=
  LinearMap.liftBaseChange (R ⊗[K] S) (unitLinear K R S N)

theorem forward_tmul (r : R) (s : S) (n : N) :
    forward K R S N ((r ⊗ₜ[K] s) ⊗ₜ[S] n) = r ⊗ₜ[K] (s • n) := by
  change (r * 1) ⊗ₜ[K] (s • n) = r ⊗ₜ[K] (s • n)
  rw [mul_one]

def inverseK : R ⊗[K] N →ₗ[K] (R ⊗[K] S) ⊗[S] N :=
  TensorProduct.lift
    { toFun := fun r =>
        { toFun := fun n => (r ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n
          map_add' := by intro n n'; rw [TensorProduct.tmul_add]
          map_smul' := by
            intro k n
            rw [TensorProduct.tmul_smul]
            rfl }
      map_add' := by
        intro r r'
        apply LinearMap.ext
        intro n
        change ((r + r') ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n =
          (r ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n + (r' ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n
        rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
      map_smul' := by
        intro k r
        apply LinearMap.ext
        intro n
        change ((k • r) ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n = k • ((r ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n)
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul'] }

theorem inverseK_tmul (r : R) (n : N) :
    inverseK K R S N (r ⊗ₜ[K] n) = (r ⊗ₜ[K] (1 : S)) ⊗ₜ[S] n := rfl

theorem left_inverse : Function.LeftInverse (inverseK K R S N) (forward K R S N) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a n =>
    induction a using TensorProduct.inductionOn with
    | tmul r s =>
      rw [forward_tmul, inverseK_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      change (((1 : R) ⊗ₜ[K] s) * (r ⊗ₜ[K] (1 : S))) ⊗ₜ[S] n = (r ⊗ₜ[K] s) ⊗ₜ[S] n
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem right_inverse : Function.RightInverse (inverseK K R S N) (forward K R S N) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r n => rw [inverseK_tmul, forward_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

def equiv : (R ⊗[K] S) ⊗[S] N ≃ₗ[R ⊗[K] S] target K R S N :=
  LinearEquiv.ofBijective (forward K R S N)
    ⟨(left_inverse K R S N).injective, (right_inverse K R S N).surjective⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorRankOne
