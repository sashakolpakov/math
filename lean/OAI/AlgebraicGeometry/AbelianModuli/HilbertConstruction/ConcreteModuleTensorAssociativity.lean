import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorComparison

/-! # Concrete Module Tensor Associativity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteModuleTensorAssociativity

noncomputable section

/-! Associativity of the actual sheafified tensor product for arbitrary module sheaves. -/
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
universe u
local instance actualAssocModuleMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Module.SheafMonoidal.moduleMonoidalCategory X

def actualModuleTensorAssoc {X : Scheme.{u}} (M N P : X.Modules) :
    Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule M N) P ≅ Tensor.ProductSheaf.tensorModule M (Tensor.ProductSheaf.tensorModule N P) :=
  (Module.MonoidalTensorComparison.moduleMonoidalTensorIso (Tensor.ProductSheaf.tensorModule M N) P).symm ≪≫
    ((Module.MonoidalTensorComparison.moduleMonoidalTensorIso M N).symm ⊗ᵢ Iso.refl P) ≪≫
    α_ M N P ≪≫ (Iso.refl M ⊗ᵢ Module.MonoidalTensorComparison.moduleMonoidalTensorIso N P) ≪≫
    Module.MonoidalTensorComparison.moduleMonoidalTensorIso M (Tensor.ProductSheaf.tensorModule N P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteModuleTensorAssociativity
