import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MixedTensor
import Mathlib.RingTheory.TensorProduct.Maps

/-! # External Tensor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensor

noncomputable section

/-! The external tensor product carries the action of the product
algebra: (r ⊗ s)(m ⊗ n) = rm ⊗ sn. The action is bundled so that the
two copies of a ring remain distinct even on a diagonal. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (K R S : Type u) [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [mK : Module K M] [Module R M] [mTower : IsScalarTower K R M]
  [Module K N] [Module S N] [IsScalarTower K S N]

def action : R ⊗[K] S →ₐ[K] Module.End K (M ⊗[K] N) :=
  Algebra.TensorProduct.lift
    ((Module.End.rTensorAlgHom K M N).comp (Algebra.lsmul K K M : R →ₐ[K] Module.End K M))
    ((Module.End.lTensorAlgHom K N M).comp (Algebra.lsmul K K N : S →ₐ[K] Module.End K N))
    (by intro r s; apply LinearMap.ext; intro x; induction x using TensorProduct.inductionOn with
        | tmul m n => rfl
        | add x y hx hy => simp only [map_add, hx, hy])

@[instance_reducible]
def module : Module (R ⊗[K] S) (M ⊗[K] N) :=
  Module.compHom (M ⊗[K] N) (action K R S M N).toRingHom

attribute [local instance] module

def obj : ModuleCat.{u} (R ⊗[K] S) :=
  .of (R ⊗[K] S) (M ⊗[K] N)

theorem smul_tmul (r : R) (s : S) (m : M) (n : N) :
    (r ⊗ₜ[K] s) • (m ⊗ₜ[K] n : obj K R S M N) = (r • m) ⊗ₜ[K] (s • n) := rfl

theorem hom_ext {P : ModuleCat.{u} (R ⊗[K] S)}
    {f g : obj K R S M N ⟶ P}
    (h : ∀ m n, f (m ⊗ₜ[K] n) = g (m ⊗ₜ[K] n)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add x y hx hy => simp only [map_add, hx, hy]

variable {M N}
  {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
  [mK' : Module K M'] [Module R M'] [IsScalarTower K R M']
  [Module K N'] [Module S N'] [IsScalarTower K S N']

def map (f : M →ₗ[R] M') (g : N →ₗ[S] N') :
    obj K R S M N ⟶ obj K R S M' N' :=
  ModuleCat.ofHom
    { TensorProduct.map (f.restrictScalars K) (g.restrictScalars K) with
      map_smul' := by
        intro a x
        change TensorProduct.map (f.restrictScalars K) (g.restrictScalars K) (a • x) =
          a • TensorProduct.map (f.restrictScalars K) (g.restrictScalars K) x
        induction a using TensorProduct.inductionOn with
        | tmul r s =>
          induction x using TensorProduct.inductionOn with
          | tmul m n => simp only [smul_tmul, TensorProduct.map_tmul, LinearMap.coe_restrictScalars, f.map_smul, g.map_smul]
          | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | add a b ha hb => simp only [add_smul, map_add, ha, hb] }

theorem map_tmul (f : M →ₗ[R] M') (g : N →ₗ[S] N') (m : M) (n : N) :
    ExternalTensor.map K R S f g (m ⊗ₜ[K] n) = f m ⊗ₜ[K] g n := rfl

def congr (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[S] N') :
    obj K R S M N ≅ obj K R S M' N' where
  hom := ExternalTensor.map K R S eM.toLinearMap eN.toLinearMap
  inv := ExternalTensor.map K R S eM.symm.toLinearMap eN.symm.toLinearMap
  hom_inv_id := by
    apply ExternalTensor.hom_ext K R S M N
    intro m n
    change eM.symm (eM m) ⊗ₜ[K] eN.symm (eN n) = m ⊗ₜ[K] n
    rw [eM.symm_apply_apply, eN.symm_apply_apply]
  inv_hom_id := by
    apply ExternalTensor.hom_ext K R S M' N'
    intro m n
    change eM (eM.symm m) ⊗ₜ[K] eN (eN.symm n) = m ⊗ₜ[K] n
    rw [eM.apply_symm_apply, eN.apply_symm_apply]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensor
