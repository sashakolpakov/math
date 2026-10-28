import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient

/-! # Refined Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedFactorization.CechPresheafRefinedFactorization

noncomputable section

/-! The actual projected presheaf Cech refinement is refinement of
the image cover followed by inverse tuple-product reindexing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts.{0} A] in
theorem bicomplex : RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r K =
    RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap V (F.obj ∘ U) r K ≫
      (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).inv := rfl

theorem total : RefinedReindex.CechPresheafRefinedReindex.map F U V r K =
    RefinementCoefficient.CechPresheafRefinementCoefficient.map V (F.obj ∘ U) r K ≫
      (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K) (.up ℕ)).inv :=
  (congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex F U V r K)).trans
    (HomologicalComplex₂.total.map_comp _ _ (.up ℕ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedFactorization.CechPresheafRefinedFactorization
