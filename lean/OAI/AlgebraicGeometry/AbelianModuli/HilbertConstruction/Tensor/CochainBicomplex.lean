import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Grp.Abelian

/-! # Cochain Bicomplex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CochainBicomplex

noncomputable section

/-! The actual tensor bicomplex of two cochain complexes, with its underlying additive bicomplex. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]

def tensorCochainMap (D : CochainComplex (ModuleCat.{u} R) ℕ)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Module.TensorFunctor.ModuleTensorFunctor.complex M D ⟶ Module.TensorFunctor.ModuleTensorFunctor.complex N D where
  f n := ModuleCat.ofHom (f.hom.rTensor (D.X n))
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

def tensorCochainFunctor (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := Module.TensorFunctor.ModuleTensorFunctor.complex M D
  map f := tensorCochainMap D f
  map_id _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp _ _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

instance tensorCochainFunctor_additive (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    (tensorCochainFunctor D).Additive where
  map_add := by
    intros
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact TensorProduct.add_tmul _ _ _

def tensorCochainBicomplex (C D : CochainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((tensorCochainFunctor D).mapHomologicalComplex (.up ℕ)).obj C

def tensorCochainBicomplexAb (C D : CochainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).mapHomologicalComplex
    (.up ℕ)).obj (tensorCochainBicomplex C D)

theorem tensorCochainBicomplexAb_row (C D : CochainComplex (ModuleCat.{u} R) ℕ) (p : ℕ) :
    (tensorCochainBicomplexAb C D).X p =
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (Module.TensorFunctor.ModuleTensorFunctor.complex (C.X p) D) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CochainBicomplex
