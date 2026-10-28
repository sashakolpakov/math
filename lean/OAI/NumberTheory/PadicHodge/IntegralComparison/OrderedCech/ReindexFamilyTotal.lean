import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal

/-! # Reindex Family Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyTotal

noncomputable section

/-! The literal cover-family identifications extend to ordered total
complexes and their original common-cover homology comparisons. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]

section Single
variable {ι : Type u} [LinearOrder ι] (U : ι → C) (U' : ι → D) (hU : r.obj ∘ U = U')
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

def familyBicomplexIso :
    ((Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).obj
      (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((Functor.Projection.functor U').mapHomologicalComplex (.up ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => ReindexCoordinates.familyIso r U U' hU (K.X q))
    (fun q q' _ => (ReindexCoordinates.family_naturality r U U' hU (K.X q) (K.d q q')).symm)

def familyTotalIso :
    (TotalProjection.ordered U).obj
      (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≅
    (TotalProjection.ordered U').obj K :=
  HomologicalComplex₂.total.mapIso (familyBicomplexIso r U U' hU K) (.up ℕ)

omit [HasCoproducts A] in
theorem familyBicomplexIso_refl :
    familyBicomplexIso r U (r.obj ∘ U) rfl K = ReindexTotal.bicomplexIso r U K := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext q
  change (Reindex.iso r U (K.X q)).hom ≫ 𝟙 _ =
    (Reindex.iso r U (K.X q)).hom
  exact Category.comp_id _

theorem familyTotalIso_refl : familyTotalIso r U (r.obj ∘ U) rfl K = ReindexTotal.totalIso r U K := by
  dsimp only [familyTotalIso]
  rw [familyBicomplexIso_refl]
  rfl
end Single

section Refinement
variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (U : ι → C) (V : κ → C)
  (ρ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (U' : ι → D) (V' : κ → D) (hU : r.obj ∘ U = U') (hV : r.obj ∘ V = V')
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts A] in
theorem family_bicomplex_refinement :
    OrderedCech.Refinement.bicomplexMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (familyBicomplexIso r V V' hV K).hom =
    (familyBicomplexIso r U U' hU K).hom ≫ OrderedCech.Refinement.bicomplexMap U' V'
      (ReindexFamilyRefinement.familyRefinement r U V ρ U' V' hU hV) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact ReindexFamilyRefinement.family_refinement r U V ρ U' V' hU hV (K.X q)

theorem family_total_refinement :
    OrderedCech.Refinement.totalMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (familyTotalIso r V V' hV K).hom =
    (familyTotalIso r U U' hU K).hom ≫ OrderedCech.Refinement.totalMap U' V'
      (ReindexFamilyRefinement.familyRefinement r U V ρ U' V' hU hV) K := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (family_bicomplex_refinement r U V ρ U' V' hU hV K)).trans (T.map_comp _ _))

theorem family_homology_refinement (q : ℕ) :
    homologyMap (OrderedCech.Refinement.totalMap U V ρ
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q ≫
      homologyMap (familyTotalIso r V V' hV K).hom q =
    homologyMap (familyTotalIso r U U' hU K).hom q ≫
      homologyMap (OrderedCech.Refinement.totalMap U' V'
        (ReindexFamilyRefinement.familyRefinement r U V ρ U' V' hU hV) K) q := by
  simpa only [homologyMap_comp] using
    congrArg (fun a => homologyMap a q) (family_total_refinement r U V ρ U' V' hU hV K)
end Refinement

variable {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → C) (V : κ → C) (W : ν → C)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (t : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V)
  (U' : ι → D) (V' : κ → D) (W' : ν → D)
  (hU : r.obj ∘ U = U') (hV : r.obj ∘ V = V') (hW : r.obj ∘ W = W')
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ) (q : ℕ)
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W t
    (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V' W'
    (ReindexFamilyRefinement.familyRefinement r V W t V' W' hV hW) K) q)]

theorem family_comparison :
    (homologyMap (OrderedCech.Refinement.totalMap U W s
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q ≫
      inv (homologyMap (OrderedCech.Refinement.totalMap V W t
        (((ReindexTotal.restriction r).mapHomologicalComplex (.up ℕ)).obj K)) q)) ≫
        homologyMap (familyTotalIso r V V' hV K).hom q =
    homologyMap (familyTotalIso r U U' hU K).hom q ≫
      homologyMap (OrderedCech.Refinement.totalMap U' W'
        (ReindexFamilyRefinement.familyRefinement r U W s U' W' hU hW) K) q ≫
      inv (homologyMap (OrderedCech.Refinement.totalMap V' W'
        (ReindexFamilyRefinement.familyRefinement r V W t V' W' hV hW) K) q) := by
  apply (cancel_mono (homologyMap (OrderedCech.Refinement.totalMap V' W'
    (ReindexFamilyRefinement.familyRefinement r V W t V' W' hV hW) K) q)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← family_homology_refinement r V W t V' W' hV hW K q, IsIso.inv_hom_id_assoc]
  exact family_homology_refinement r U W s U' W' hU hW K q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyTotal
