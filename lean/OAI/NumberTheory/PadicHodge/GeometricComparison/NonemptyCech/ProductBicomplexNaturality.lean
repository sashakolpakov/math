import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Product Bicomplex Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplexNaturality.NonemptyCechProductBicomplexNaturality

noncomputable section

/-! The original product-cover base-change isomorphism for Cech
bicomplexes is natural in maps of the coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b w
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]
  (F : C ⥤ D) {ι : Type w} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  {K L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (α : K ⟶ L)

theorem natural : ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).map
    (((ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F).mapHomologicalComplex (.up ℕ)).map α) ≫
      (ProductBicomplex.NonemptyCechProductBicomplex.iso F U L).hom =
    (ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).hom ≫
      ((IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U)).mapHomologicalComplex (.up ℕ)).map α :=
  (NatIso.mapHomologicalComplex (ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.iso F U) (.up ℕ)).hom.naturality α

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplexNaturality.NonemptyCechProductBicomplexNaturality
