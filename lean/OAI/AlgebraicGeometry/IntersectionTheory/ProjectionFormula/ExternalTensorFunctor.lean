import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensor

/-! # External Tensor Functor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFunctor

noncomputable section

/-! Over a field the external tensor product is an exact additive
functor in either input. This file bundles the first-input functor
and its actual short-exact-sequence transport. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (K R S : Type u) [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

abbrev scalar (M : ModuleCat.{u} R) : Module K M := Module.restrictScalars K R M

theorem tower (M : ModuleCat.{u} R) :
    let := scalar K R M
    IsScalarTower K R M := IsScalarTower.restrictScalars K R M

attribute [local instance] scalar tower ExternalTensor.module

variable (N : ModuleCat.{u} S)

def tensor : ModuleCat.{u} R ⥤ ModuleCat.{u} (R ⊗[K] S) where
  obj M := ExternalTensor.obj K R S M N
  map f := ExternalTensor.map K R S f.hom (LinearMap.id : N →ₗ[S] N)
  map_id M := by
    apply ExternalTensor.hom_ext K R S M N
    intro m n
    rfl
  map_comp f g := by
    apply ExternalTensor.hom_ext K R S _ N
    intro m n
    rfl

instance : (tensor K R S N).Additive where
  map_add := by
    intro M M' f g
    apply ExternalTensor.hom_ext K R S M N
    intro m n
    exact TensorProduct.add_tmul (f m) (g m) n

theorem map_exact (T : ShortComplex (ModuleCat.{u} R)) (hT : T.Exact) :
    (T.map (tensor K R S N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact Module.Flat.rTensor_exact N
    (show Function.Exact (T.f.hom.restrictScalars K) (T.g.hom.restrictScalars K) from hT)

instance : (tensor K R S N).PreservesHomology :=
  ((Functor.exact_tfae (tensor K R S N)).out 2 3).mp (map_exact K R S N)

theorem map_shortExact (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) :
    (T.map (tensor K R S N)).ShortExact := by
  let := hT.mono_f
  let := hT.epi_g
  exact hT.map (tensor K R S N)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorFunctor
