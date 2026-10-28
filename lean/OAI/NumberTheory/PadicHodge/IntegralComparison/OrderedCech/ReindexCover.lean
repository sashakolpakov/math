import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal

/-! # Reindex Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCover.Total

noncomputable section

/-! The actual ordered refinement and common-cover homology maps
commute with finite-limit-preserving changes of open diagrams. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (U : ι → C) (V : κ → C)
  (ρ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts A] in
theorem bicomplex_refinement :
    Refinement.bicomplexMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫ (ReindexTotal.bicomplexIso r V K).hom =
      (ReindexTotal.bicomplexIso r U K).hom ≫ Refinement.bicomplexMap (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact ReindexRefinement.refinement r U (K.X q) V ρ

theorem total_refinement :
    Refinement.totalMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫ (ReindexTotal.totalIso r V K).hom =
      (ReindexTotal.totalIso r U K).hom ≫ Refinement.totalMap (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) K := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex_refinement r U V ρ K)).trans (T.map_comp _ _))

theorem homology_refinement (q : ℕ) :
    homologyMap (Refinement.totalMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q ≫
      homologyMap (ReindexTotal.totalIso r V K).hom q =
    homologyMap (ReindexTotal.totalIso r U K).hom q ≫
      homologyMap (Refinement.totalMap (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) K) q := by
  simpa only [homologyMap_comp] using
    congrArg (fun a => homologyMap a q) (total_refinement r U V ρ K)

variable {ν : Type u} [LinearOrder ν] (W : ν → C)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (t : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V) (q : ℕ)
  [IsIso (homologyMap (Refinement.totalMap V W t
    (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q)]
  [IsIso (homologyMap (Refinement.totalMap (r.obj ∘ V) (r.obj ∘ W)
    (Cech.BaseChangeRefinement.refinement r V W t) K) q)]

theorem comparison :
    (homologyMap (Refinement.totalMap U W s
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q ≫
      inv (homologyMap (Refinement.totalMap V W t
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q)) ≫
        homologyMap (ReindexTotal.totalIso r V K).hom q =
    homologyMap (ReindexTotal.totalIso r U K).hom q ≫
      homologyMap (Refinement.totalMap (r.obj ∘ U) (r.obj ∘ W)
        (Cech.BaseChangeRefinement.refinement r U W s) K) q ≫
      inv (homologyMap (Refinement.totalMap (r.obj ∘ V) (r.obj ∘ W)
        (Cech.BaseChangeRefinement.refinement r V W t) K) q) := by
  apply (cancel_mono (homologyMap (Refinement.totalMap (r.obj ∘ V) (r.obj ∘ W)
    (Cech.BaseChangeRefinement.refinement r V W t) K) q)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← homology_refinement r V W t K q, IsIso.inv_hom_id_assoc]
  exact homology_refinement r U W s K q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCover.Total
