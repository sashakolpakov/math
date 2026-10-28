import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Module Tensor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor

noncomputable section

/-! Scalar tensor as an additive functor, with explicit module universes. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R]
variable (A : Type v) [AddCommGroup A] [Module R A]

def tensor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (A ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.lTensor A)
  map_id M := by apply ModuleCat.hom_ext; apply TensorProduct.ext; ext a m; rfl
  map_comp f g := by apply ModuleCat.hom_ext; apply TensorProduct.ext; ext a m; rfl

instance : (tensor (R := R) A).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a m
    exact TensorProduct.tmul_add _ _ _

abbrev complex (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  ((tensor A).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

abbrev map {C D : CochainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D) :
    complex A C ⟶ complex A D :=
  ((tensor A).mapHomologicalComplex (ComplexShape.up ℕ)).map φ

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor
