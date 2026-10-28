import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Equality And Pullback Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EqualityAndPullbackValues

noncomputable section

/-! Global sections are determined on a covering family of opens. Actual
pullback section values on inverse-image opens are the adjunction-unit values. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u v
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}}

theorem moduleSection_eq_of_cover (M : X.Modules) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (s t : Line.Bundles.structureModule X ⟶ M)
    (h : ∀ i, s.app (U i) (1 : Γ(X, U i)) = t.app (U i) (1 : Γ(X, U i))) : s = t := by
  apply (Global.Sections.moduleSectionHomEquiv M).injective
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq' U ⊤ (fun i => (U i).leTop)
    (by intro x _; exact Opens.mem_iSup.mpr (hU x))
  intro i
  exact (Gluing.moduleSectionHomEquiv_restrict M s (U i)).trans
    ((h i).trans (Gluing.moduleSectionHomEquiv_restrict M t (U i)).symm)

theorem pullbackSection_value_on_preimage (f : X ⟶ Y) {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) (U : Y.Opens) :
    (Ample.LineBundles.pullbackSection f s).app (f ⁻¹ᵁ U) (1 : Γ(X, f ⁻¹ᵁ U)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U
        (s.app U (1 : Γ(Y, U))) := by
  let e := Line.Bundles.structureModulePullbackIso f
  let v := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have he : e.hom ≫ Ample.LineBundles.pullbackSection f s = (Scheme.Modules.pullback f).map s := by
    simp only [Ample.LineBundles.pullbackSection, e, Iso.hom_inv_id_assoc]
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pushforward f).map e.hom = v := Tensor.PullbackUnits.structureModulePullbackIso_unit f
  have h : v ≫ (Scheme.Modules.pushforward f).map (Ample.LineBundles.pullbackSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
    rw [← hu, Category.assoc, ← Functor.map_comp, he]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s).symm
  have hv := congrArg (fun c : Line.Bundles.structureModule Y ⟶
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) =>
      c.app U (1 : Γ(Y, U))) h
  change (Ample.LineBundles.pullbackSection f s).app (f ⁻¹ᵁ U) (f.app U (1 : Γ(Y, U))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U
      (s.app U (1 : Γ(Y, U))) at hv
  simpa only [map_one] using hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EqualityAndPullbackValues
