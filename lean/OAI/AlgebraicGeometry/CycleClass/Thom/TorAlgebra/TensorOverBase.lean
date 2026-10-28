import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Tensor Over Base -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase

noncomputable section

/-! Tensoring an algebra module over its base ring retains the
algebra action. Its underlying base module is the native tensor functor,
and it preserves finite colimits without a flatness hypothesis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (N : ModuleCat.{u} R)

local instance moduleCarrier (M : ModuleCat.{u} A) : Module R M := Module.compHom M (algebraMap R A)
local instance scalarTowerCarrier (M : ModuleCat.{u} A) : IsScalarTower R A M :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def tensorOverBase : ModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of A (M ⊗[R] N)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.rTensor R N f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.rTensor_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.rTensor_comp g.hom f.hom

instance : (tensorOverBase R A N).Additive where
  map_add := by
    intro M M' f g
    apply ModuleCat.hom_ext
    exact map_add (TensorProduct.AlgebraTensorModule.rTensor R N) f.hom g.hom

theorem tensor_algebraMap_smul (M : ModuleCat.{u} A) (r : R) (t : M ⊗[R] N) :
    (algebraMap R A r) • t = r • t := IsScalarTower.algebraMap_smul A r t

def underlyingComponent (M : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj ((tensorOverBase R A N).obj M) ≃ₗ[R]
      (tensorRight N).obj ((ModuleCat.restrictScalars (algebraMap R A)).obj M) where
  __ := AddEquiv.refl (M ⊗[R] N)
  map_smul' r t := tensor_algebraMap_smul R A N M r t

def underlyingIso : tensorOverBase R A N ⋙ ModuleCat.restrictScalars (algebraMap R A) ≅
    ModuleCat.restrictScalars (algebraMap R A) ⋙ tensorRight N :=
  NatIso.ofComponents (fun M => (underlyingComponent R A N M).toModuleIso)
    (by intro M M' f; ext t; rfl)

theorem map_exact_of_epi (K : ShortComplex (ModuleCat.{u} A)) (hK : K.Exact) [Epi K.g] :
    (K.map (tensorOverBase R A N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact rTensor_exact N (f := K.f.hom.restrictScalars R) (g := K.g.hom.restrictScalars R)
    hK ((ModuleCat.epi_iff_surjective K.g).mp inferInstance)

instance tensorOverBase_preservesFiniteColimits : PreservesFiniteColimits (tensorOverBase R A N) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (tensorOverBase R A N)).mpr
  intro K hK
  let : Epi K.g := hK.epi_g
  refine ⟨map_exact_of_epi R A N K hK.exact, ?_⟩
  apply (ModuleCat.epi_iff_surjective ((tensorOverBase R A N).map K.g)).mpr
  exact LinearMap.rTensor_surjective N (g := K.g.hom.restrictScalars R) hK.moduleCat_surjective_g

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase
