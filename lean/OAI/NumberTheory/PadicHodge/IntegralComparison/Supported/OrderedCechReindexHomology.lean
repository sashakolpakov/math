import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech

/-! # Ordered Cech Reindex Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindexHomology

noncomputable section

/-! The canonical supported-to-global cohomology map is unchanged
by finite-product-preserving reindexing of the actual Čech cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_edge {A : Type*} [Category A]
    {S₁ S₂ T₁ T₂ Z : A} (e₁ : S₁ ≅ T₁) (e₂ : S₂ ≅ T₂)
    (s : S₁ ⟶ S₂) (t : T₁ ⟶ T₂) (a : S₁ ⟶ Z) (b : S₂ ⟶ Z)
    (he : s ≫ e₂.hom = e₁.hom ≫ t) (ha : s ≫ b = a) :
    t ≫ (e₂.inv ≫ b) = e₁.inv ≫ a := by
  apply (cancel_epi e₁.hom).mp
  rw [← Category.assoc e₁.hom t (e₂.inv ≫ b), ← he]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ha

universe u
variable (R : Type (u + 1)) [CommRing R] (X : TopCat.{u})
  {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (F : D ⥤ Opens X)
  {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 2} R)) ℕ)
  (hO : ∀ i, F.obj (r.obj (U i)) ≤ O)
  (hcoverC : (r ⋙ F).obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hcoverD : F.obj (⊤_ D) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hrowsC : ∀ q n,
    ((OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X (r ⋙ F) U K).X q).ExactAt (n + 1))
  (hrowsD : ∀ q n,
    ((OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R X F (r.obj ∘ U) K).X q).ExactAt (n + 1))
  (hglobalC : (r ⋙ F).obj (⊤_ C) ⊔ O = ⊤)
  (hglobalD : F.obj (⊤_ D) ⊔ O = ⊤)

theorem comparison (i : ℕ) :
    HomologicalComplex.homologyMap (OrderedCechReindex.totalIso R X r F U K).hom i ≫
      OrderedCech.Comparison.forgetSupport.{u+1,u,u,u+2}
        R X F (r.obj ∘ U) O K hO hcoverD hrowsD hglobalD i =
    OrderedCech.Comparison.forgetSupport.{u+1,u,u,u+2}
      R X (r ⋙ F) U O K hO hcoverC hrowsC hglobalC i := by
  have he := congrArg (fun a => HomologicalComplex.homologyMap a i)
    (OrderedCechReindex.edge R X r F U O K hO)
  have ha := congrArg (fun a => HomologicalComplex.homologyMap a i)
    (OrderedCechReindex.extension R X r F O K hglobalC hglobalD)
  simp only [HomologicalComplex.homologyMap_comp] at he ha
  exact inverse_edge
    (OrderedCech.Comparison.homologyIso.{u+1,u,u,u+2}
      R X (r ⋙ F) U O K hO hcoverC hrowsC i)
    (OrderedCech.Comparison.homologyIso.{u+1,u,u,u+2}
      R X F (r.obj ∘ U) O K hO hcoverD hrowsD i)
    (HomologicalComplex.homologyMap (OrderedCechReindex.sourceIso R X r F O K).hom i)
    (HomologicalComplex.homologyMap (OrderedCechReindex.totalIso R X r F U K).hom i)
    (HomologicalComplex.homologyMap
      (SectionsExcision.extensionComplex O ((r ⋙ F).obj (⊤_ C)) hglobalC K) i)
    (HomologicalComplex.homologyMap
      (SectionsExcision.extensionComplex O (F.obj (⊤_ D)) hglobalD K) i)
    he ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindexHomology
