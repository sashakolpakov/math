import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorInverse
import Mathlib.CategoryTheory.Equivalence

/-! # Tensor Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence

noncomputable section

/-! Tensoring with an actual line bundle is an equivalence, using its constructed reciprocal frame bundle as inverse. -/

open _root_.CategoryTheory MonoidalCategory _root_.AlgebraicGeometry

universe u v

def tensorLeftEquivalenceOfInverse {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M N : C) (e : M ⊗ N ≅ 𝟙_ C) (f : N ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft N)
    ((tensorLeftTensor N M).symm ≪≫ (curriedTensor C).mapIso f ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor M N).symm ≪≫ (curriedTensor C).mapIso e ≪≫ leftUnitorNatIso C)

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := Module.SheafMonoidal.moduleMonoidalCategory X
local instance (X : Scheme.{u}) : SymmetricCategory X.Modules := Module.SheafMonoidal.moduleSymmetricCategory X

def lineBundleTensorEquivalence {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) : X.Modules ≌ X.Modules :=
  tensorLeftEquivalenceOfInverse L.sheaf L.reciprocalFrameBundle.sheaf
    (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf L.reciprocalFrameBundle.sheaf ≪≫
      L.tensorReciprocalFrameIso ≪≫ (Module.MonoidalTensorComparison.moduleMonoidalUnitIso X).symm)
    (Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.reciprocalFrameBundle.sheaf L.sheaf ≪≫
      L.reciprocalFrameTensorIso ≪≫ (Module.MonoidalTensorComparison.moduleMonoidalUnitIso X).symm)

def lineBundleRightTensorEquivalence {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) : X.Modules ≌ X.Modules :=
  (lineBundleTensorEquivalence L).changeFunctor (BraidedCategory.tensorLeftIsoTensorRight L.sheaf)

def lineBundleTensorEquivalence_objIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (M : X.Modules) :
    (lineBundleTensorEquivalence L).functor.obj M ≅ Tensor.ProductSheaf.tensorModule L.sheaf M :=
  Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf M

def lineBundleRightTensorEquivalence_objIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (M : X.Modules) :
    (lineBundleRightTensorEquivalence L).functor.obj M ≅ Tensor.ProductSheaf.tensorModule M L.sheaf :=
  Module.MonoidalTensorComparison.moduleMonoidalTensorIso M L.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
