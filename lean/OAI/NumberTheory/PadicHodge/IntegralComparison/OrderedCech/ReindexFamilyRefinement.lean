import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexRefinement

/-! # Reindex Family Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyRefinement

noncomputable section

/-! Literal equality of the image cover families preserves the
original ordered reindexing and its refinement square. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (U : ι → C) (V : κ → C)
  (ρ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (U' : ι → D) (V' : κ → D) (hU : r.obj ∘ U = U') (hV : r.obj ∘ V = V')

def familyRefinement : FormalCoproduct.mk κ V' ⟶ FormalCoproduct.mk ι U' :=
  eqToHom (congrArg (FormalCoproduct.mk κ) hV).symm ≫
    Cech.BaseChangeRefinement.refinement r U V ρ ≫
      eqToHom (congrArg (FormalCoproduct.mk ι) hU)

variable {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : Dᵒᵖ ⥤ A)

omit [HasCoproducts A] in
theorem family_refinement :
    Refinement.map U V ρ (r.op ⋙ P) ≫ (ReindexCoordinates.familyIso r V V' hV P).hom =
      (ReindexCoordinates.familyIso r U U' hU P).hom ≫
        Refinement.map U' V' (familyRefinement r U V ρ U' V' hU hV) P := by
  subst U'
  subst V'
  simpa only [ReindexCoordinates.familyIso, familyRefinement, eqToIso_refl, Iso.trans_refl,
    eqToHom_refl, Category.id_comp, Category.comp_id] using ReindexRefinement.refinement r U P V ρ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexFamilyRefinement
