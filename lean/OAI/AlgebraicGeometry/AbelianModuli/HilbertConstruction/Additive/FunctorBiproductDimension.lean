import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteBiproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteCoproducts
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Functor Biproduct Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorBiproductDimension

noncomputable section

/-! An additive functor to finite-dimensional vector spaces takes a finite biproduct to the sum of the component dimensions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w

theorem additive_functor_biproduct_finrank
    {C : Type v} [Category.{w} C] [Preadditive C]
    {K : Type u} [Field K] (F : C ⥤ ModuleCat.{u} K) [F.Additive]
    {I : Type u} [Fintype I] (M : I → C) [HasBiproduct M]
    (hM : ∀ i, Module.Finite K (F.obj (M i))) :
    Module.finrank K (F.obj (⨁ M)) = ∑ i, Module.finrank K (F.obj (M i)) := by
  let : HasBiproduct (F.obj ∘ M) := HasBiproduct.of_hasProduct (F.obj ∘ M)
  let : ∀ i, Module.Finite K (F.obj (M i)) := hM
  have := FunctorFiniteBiproducts.additive_functor_preserves_finite_biproduct F M
  let e : F.obj (⨁ M) ≅ ModuleCat.of K (∀ i, F.obj (M i)) :=
    F.mapBiproduct M ≪≫ biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)
  exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_pi_fintype K)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorBiproductDimension
