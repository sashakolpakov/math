import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechPullbackSectionNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Global Section Pullback Values -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalSectionPullbackValues

noncomputable section

/-! Pullback of literal top sections is semilinear and agrees with
pullback of their actual structure-module morphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
universe u

def pullbackTopLinearMap {X Y : Scheme.{u}} (a : Y ⟶ X) (M : X.Modules) :
    Γ(M, ⊤) →ₛₗ[a.appTop.hom] Γ((Scheme.Modules.pullback a).obj M, ⊤) where
  toFun := CechPullbackSectionNormalization.pullbackTopSection a M
  map_add' s t := by
    simp only [CechPullbackSectionNormalization.pullbackTopSection, map_add]
  map_smul' r s := by
    dsimp only [CechPullbackSectionNormalization.pullbackTopSection]
    have hm := (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤).map_smulₛₗ r s
    rw [show Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤ (r • s) =
      a.app ⊤ r • Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤ s from hm]
    rw [Scheme.Modules.map_smul]
    change Y.presheaf.map (𝟙 (op ⊤)) (a.appTop r) • _ = _
    rw [Y.presheaf.map_id]
    rfl

theorem pullbackTopSection_hom_value
    {X Y : Scheme.{u}} (a : Y ⟶ X) {M : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    CechPullbackSectionNormalization.pullbackTopSection a M (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) =
      AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s) := by
  have : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward a).IsRightAdjoint
  let F := Scheme.Modules.pushforward a
  have he : ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _)
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom =
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hn : s ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M =
      SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom ≫
        F.map (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s) := by
    rw [← he]
    change _ = (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≫
      F.map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom ≫ F.map (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s)
    rw [← F.map_comp]
    have hc : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom ≫ AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s =
        (Scheme.Modules.pullback a).map s := by
      simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Iso.hom_inv_id_assoc]
    rw [hc]
    exact (Scheme.Modules.pullbackPushforwardAdjunction a).unit.naturality s
  have hv := congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ F.obj ((Scheme.Modules.pullback a).obj M) =>
    q.app ⊤ (1 : Γ(X, ⊤))) hn
  have hv' : Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤ (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) =
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s).app (a ⁻¹ᵁ ⊤) (1 : Γ(Y, a ⁻¹ᵁ ⊤)) := by
    change Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map a M ⊤ (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) =
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s).app (a ⁻¹ᵁ ⊤) (a.app ⊤ 1) at hv
    rw [map_one] at hv
    exact hv
  dsimp only [CechPullbackSectionNormalization.pullbackTopSection]
  rw [hv']
  have ht := PresheafOfModules.naturality_apply (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s).val
    (eqToHom a.preimage_top.symm).op (1 : Γ(Y, a ⁻¹ᵁ ⊤))
  have ht' := ht.symm
  change ((Scheme.Modules.pullback a).obj M).presheaf.map (eqToHom a.preimage_top.symm).op
      ((AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s).app (a ⁻¹ᵁ ⊤) (1 : Γ(Y, a ⁻¹ᵁ ⊤))) =
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s).app ⊤ (Y.presheaf.map (eqToHom a.preimage_top.symm).op
      (1 : Γ(Y, a ⁻¹ᵁ ⊤))) at ht'
  rw [show Y.presheaf.map (eqToHom a.preimage_top.symm).op (1 : Γ(Y, a ⁻¹ᵁ ⊤)) = 1 from
    (Y.presheaf.map (eqToHom a.preimage_top.symm).op).hom.map_one] at ht'
  exact ht'

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalSectionPullbackValues
