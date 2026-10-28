import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedFactorization

/-! # Reindex Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexComposition.CechPresheafReindexComposition

noncomputable section

/-! Projected refinement through two indexing functors agrees with
the original projected refinement through their composite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t d e a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {E : Type d} [Category.{e} E] [Quiver.IsThin E] [HasBinaryProducts E]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A]
  (F : C ⥤ D) (G : D ⥤ E) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor ((F.obj ∘ U) ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ t)) G]
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) (F ⋙ G)]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (K : CochainComplex (Eᵒᵖ ⥤ A) ℕ)

theorem bicomplex : RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r
    (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) G).mapHomologicalComplex (.up ℕ)).obj K) =
      (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G V K).hom ≫
        RefinedReindex.CechPresheafRefinedReindex.bicomplexMap (F ⋙ G) U (G.obj ∘ V)
          (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) K := by
  apply (cancel_mono (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (F ⋙ G) U K).hom).mp
  let e := NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (F ⋙ G) U K
  let d := RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
    (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) K
  have h : (d ≫ e.inv) ≫ e.hom = d :=
    (Category.assoc d e.inv e.hom).trans
      ((congrArg (fun a => d ≫ a) e.inv_hom_id).trans (Category.comp_id d))
  exact (ReindexProduct.CechPresheafReindexProduct.bicomplex F G U V r K).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun a => (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G V K).hom ≫ a) h)).symm

variable [HasCoproducts.{0} A]

theorem total : RefinedReindex.CechPresheafRefinedReindex.map F U V r
    (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) G).mapHomologicalComplex (.up ℕ)).obj K) =
      (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G V K) (.up ℕ)).hom ≫
        RefinedReindex.CechPresheafRefinedReindex.map (F ⋙ G) U (G.obj ∘ V)
          (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) K :=
  (congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex F G U V r K)).trans
    (HomologicalComplex₂.total.map_comp _ _ (.up ℕ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexComposition.CechPresheafReindexComposition
