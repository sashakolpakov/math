import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal

/-! # Cech Reindex Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexRefinement

noncomputable section

/-! Augmented ordered refinements commute with the original product
reindexing, including the degree-zero ambient sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (U : ι → C) (V : κ → C)
  (ρ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : Dᵒᵖ ⥤ A)

omit [HasCoproducts A] in
theorem refinement :
    CechRefinement.map U V ρ (r.op ⋙ P) ≫ (CechReindex.iso r V P).hom =
      (CechReindex.iso r U P).hom ≫ CechRefinement.map (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) P := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change ((CechZero.zeroIso U (r.op ⋙ P)).hom ≫
        (CechZero.zeroIso V (r.op ⋙ P)).inv) ≫ (CechReindex.iso r V P).hom.f 0 =
      (CechReindex.iso r U P).hom.f 0 ≫ ((CechZero.zeroIso (r.obj ∘ U) P).hom ≫
        (CechZero.zeroIso (r.obj ∘ V) P).inv)
    apply (cancel_mono (CechZero.zeroIso (r.obj ∘ V) P).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [CechReindex.zero r V P, Iso.inv_hom_id_assoc, CechReindex.zero r U P]
  | succ n =>
    exact congrArg (fun a => a.f n) (OrderedCech.ReindexRefinement.refinement r U P V ρ)

variable (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts A] in
theorem bicomplex_refinement :
    CechRefinementTotal.bicomplexMap U V ρ
        (((CechReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (CechReindexTotal.bicomplexIso r V K).hom =
    (CechReindexTotal.bicomplexIso r U K).hom ≫
      CechRefinementTotal.bicomplexMap (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact refinement r U V ρ (K.X q)

theorem total_refinement :
    CechRefinementTotal.totalMap U V ρ
        (((CechReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (CechReindexTotal.totalIso r V K).hom =
    (CechReindexTotal.totalIso r U K).hom ≫
      CechRefinementTotal.totalMap (r.obj ∘ U) (r.obj ∘ V)
        (Cech.BaseChangeRefinement.refinement r U V ρ) K := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex_refinement r U V ρ K)).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexRefinement
