import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.RefinementProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinementCoefficient

/-! # Reindex Product -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexProduct.CechPresheafReindexProduct

noncomputable section

/-! Projected refinement through an intermediate category agrees
with the original refinement after passage to actual open products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

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

theorem cochain (P : Eᵒᵖ ⥤ A) :
    (NonemptyCech.Refinement.NonemptyCechRefinement.map V (F.obj ∘ U) r (G.op ⋙ P) ≫
      (NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (G.op ⋙ P)).inv) ≫
      (NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso (F ⋙ G) U P).hom =
    (NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso G V P).hom ≫
      NonemptyCech.Refinement.NonemptyCechRefinement.map (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
        (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) P := by
  let e₀ := NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U (G.op ⋙ P)
  let e₁ := NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso G (F.obj ∘ U) P
  let e₂ := NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso (F ⋙ G) U P
  let a := NonemptyCech.Refinement.NonemptyCechRefinement.map V (F.obj ∘ U) r (G.op ⋙ P)
  have h : e₀.inv ≫ e₂.hom = e₁.hom :=
    (congrArg (fun x => e₀.inv ≫ x) (NonemptyCech.ProductComposition.NonemptyCechProductComposition.composition F G U P).symm).trans
      (e₀.inv_hom_id_assoc e₁.hom)
  exact (Category.assoc a e₀.inv e₂.hom).trans
    ((congrArg (fun x => a ≫ x) h).trans
      (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.naturality G (F.obj ∘ U) V r P))

variable (K : CochainComplex (Eᵒᵖ ⥤ A) ℕ)

theorem bicomplex : RefinedReindex.CechPresheafRefinedReindex.bicomplexMap F U V r
    (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) G).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (F ⋙ G) U K).hom =
    (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G V K).hom ≫
      RefinementCoefficient.CechPresheafRefinementCoefficient.bicomplexMap (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
        (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact cochain F G U V r (K.X q)

variable [HasCoproducts.{0} A]

theorem total : RefinedReindex.CechPresheafRefinedReindex.map F U V r
    (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) G).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (F ⋙ G) U K) (.up ℕ)).hom =
    (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso G V K) (.up ℕ)).hom ≫
      RefinementCoefficient.CechPresheafRefinementCoefficient.map (G.obj ∘ V) (G.obj ∘ F.obj ∘ U)
        (NonemptyCech.RefinementProduct.NonemptyCechRefinementProduct.mappedCover G (F.obj ∘ U) V r) K :=
  (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)).symm.trans
    ((congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ)) (bicomplex F G U V r K)).trans
      (HomologicalComplex₂.total.map_comp _ _ (.up ℕ)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ReindexProduct.CechPresheafReindexProduct
