import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLocalizedExtension

/-! # Cech Selected Complement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechSelectedComplement

noncomputable section

/-! A local diagram meeting two complements in the same open has one
supported Cech edge. Its selected extension is therefore the original
support-forgetting map for the selected complement. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C)
  (O₁ O₂ : Opens X) (he : F.obj (⊤_ C) ⊓ O₁ = F.obj (⊤_ C) ⊓ O₂)
  (hc : F.obj (⊤_ C) ⊔ O₂ = ⊤)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ)

local instance coefficient_limits [UnivLE.{w,z}] : HasLimitsOfSize.{w,w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w,w,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R
local instance total_exists :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def sourceIso : OrderedCechEdge.source.{u,v,w,z} R X F O₁ K ≅
    OrderedCechEdge.source.{u,v,w,z} R X F O₂ K :=
  (NatIso.mapHomologicalComplex
    (SectionsLocalizedExtension.localIso O₁ O₂ (F.obj (⊤_ C)) he) (.up ℕ)).app K

variable (h₁ : ∀ i, F.obj (U i) ≤ O₁) (h₂ : ∀ i, F.obj (U i) ≤ O₂)

theorem edge :
    (sourceIso.{u,v,w,z} R X F O₁ O₂ he K).hom ≫
      OrderedCechEdge.map.{u,v,w,z} R X F U O₂ K h₂ =
    OrderedCechEdge.map.{u,v,w,z} R X F U O₁ K h₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, OrderedCechEdge.map,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f]
  change (SectionsLocalizedExtension.localIso O₁ O₂ (F.obj (⊤_ C)) he).hom.app
      (K.X q) ≫
      ((SectionsExcision.inclusion (F.obj (⊤_ C))
        (F.obj (⊤_ C) ⊓ O₂) inf_le_left).app (K.X q) ≫ _) ≫ _ = _
  simp only [← Category.assoc]
  erw [SectionsLocalizedExtension.codomainIso_inclusion]
  rfl

theorem globalSectionCandidate_eq :
    CechLocalizedExtension.globalSectionCandidate.{u,v,w,z} R X F O₁ O₂ he hc K =
      (sourceIso.{u,v,w,z} R X F O₁ O₂ he K).hom ≫
        SectionsExcision.extensionComplex O₂ (F.obj (⊤_ C)) hc K := by
  apply HomologicalComplex.Hom.ext
  funext q
  change (((SectionsLocalizedExtension.localIso O₁ O₂ (F.obj (⊤_ C)) he).hom.app
      (K.X q) ≫
      (SectionsExcision.excisionIso O₂ (F.obj (⊤_ C)) hc).inv.app (K.X q)) ≫
      (SectionsExcision.inclusion ⊤ O₂ le_top).app (K.X q)) = _
  exact Category.assoc _ _ _

variable (hc₁ : F.obj (⊤_ C) ⊓ O₁ ≤ ⨆ i, F.obj (U i))
  (hc₂ : F.obj (⊤_ C) ⊓ O₂ ≤ ⨆ i, F.obj (U i))
  (hr : ∀ q r,
    ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).ExactAt (r+1))

theorem forgetSupport (n : ℕ) :
    (OrderedCech.Comparison.homologyIso.{u,v,w,z} R X F U O₁ K h₁ hc₁ hr n).inv ≫
      homologyMap (CechLocalizedExtension.globalSectionCandidate.{u,v,w,z}
        R X F O₁ O₂ he hc K) n =
    OrderedCech.Comparison.forgetSupport.{u,v,w,z}
      R X F U O₂ K h₂ hc₂ hr hc n := by
  have hs : homologyMap (sourceIso.{u,v,w,z} R X F O₁ O₂ he K).hom n ≫
      homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F U O₂ K h₂) n =
    homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F U O₁ K h₁) n := by
    simpa only [homologyMap_comp] using
      congrArg (fun a => homologyMap a n) (edge.{u,v,w,z} R X F U O₁ O₂ he K h₁ h₂)
  apply (cancel_epi (OrderedCech.Comparison.homologyIso.{u,v,w,z}
    R X F U O₁ K h₁ hc₁ hr n).hom).mp
  rw [Iso.hom_inv_id_assoc]
  change _ = homologyMap (OrderedCechEdge.map.{u,v,w,z} R X F U O₁ K h₁) n ≫ _
  rw [← hs, Category.assoc, OrderedCech.Comparison.map_forgetSupport,
    globalSectionCandidate_eq, homologyMap_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechSelectedComplement
