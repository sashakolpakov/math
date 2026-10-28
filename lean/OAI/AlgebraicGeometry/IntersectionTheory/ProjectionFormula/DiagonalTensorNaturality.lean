import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor

/-! # Diagonal Tensor Naturality -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality

noncomputable section

/-! The diagonal tensor identification is natural in its first input,
with the original-ring action obtained from the first product factor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]

attribute [local instance] DiagonalTensor.diagonalAlgebra ExternalTensorFunctor.scalar
  ExternalTensorFunctor.tower ExternalTensor.module

abbrev first : R →+* DiagonalTensor.Ring K R := (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] R).toRingHom

def diagonal : ModuleCat.{u} (DiagonalTensor.Ring K R) :=
  (ModuleCat.restrictScalars (DiagonalTensor.multiplication K R)).obj (.of R R)

theorem first_smul {V : Type u} [AddCommGroup V] [Module R V]
    [Module (DiagonalTensor.Ring K R) V] [IsScalarTower (DiagonalTensor.Ring K R) R V] (r : R) (v : V) :
    first K R r • v = r • v := by
  rw [← algebraMap_smul R (first K R r)]
  have he : algebraMap (DiagonalTensor.Ring K R) R (first K R r) = r := mul_one r
  rw [he]

variable (M N : ModuleCat.{u} R)

def component :
    (ModuleCat.restrictScalars (first K R)).obj
      ((tensorRight (diagonal K R)).obj ((ExternalTensorFunctor.tensor K R R N).obj M)) ≃ₗ[R]
      M ⊗[R] N :=
  { (TensorProduct.comm (DiagonalTensor.Ring K R) (ExternalTensor.obj K R R M N) R).toAddEquiv.trans
      (DiagonalTensor.equiv K R M N).toAddEquiv with
    map_smul' := by
      intro r x
      change DiagonalTensor.equiv K R M N
        ((TensorProduct.comm (DiagonalTensor.Ring K R) (ExternalTensor.obj K R R M N) R) (first K R r • x)) =
        r • DiagonalTensor.equiv K R M N
          ((TensorProduct.comm (DiagonalTensor.Ring K R) (ExternalTensor.obj K R R M N) R) x)
      rw [map_smul]
      let y : R ⊗[DiagonalTensor.Ring K R] ExternalTensor.obj K R R M N :=
        TensorProduct.comm (DiagonalTensor.Ring K R) (ExternalTensor.obj K R R M N) R x
      exact (congrArg (DiagonalTensor.equiv K R M N) (first_smul K R r y)).trans ((DiagonalTensor.equiv K R M N).map_smul r y) }

theorem component_tmul (r : R) (m : M) (n : N) :
    component K R M N ((m ⊗ₜ[K] n) ⊗ₜ[DiagonalTensor.Ring K R] r) = r • (m ⊗ₜ[R] n) := rfl

variable {M}

def naturalIso :
    ExternalTensorFunctor.tensor K R R N ⋙ tensorRight (diagonal K R) ⋙
      ModuleCat.restrictScalars (first K R) ≅ tensorRight N :=
  NatIso.ofComponents (fun M => (component K R M N).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul x r =>
      induction x using TensorProduct.inductionOn with
      | tmul m n =>
        change (show R from r) • (f m ⊗ₜ[R] n) =
          (TensorProduct.map f.hom (LinearMap.id : N →ₗ[R] N)) ((show R from r) • (m ⊗ₜ[R] n))
        rw [map_smul, TensorProduct.map_tmul]
        rfl
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy])

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality
