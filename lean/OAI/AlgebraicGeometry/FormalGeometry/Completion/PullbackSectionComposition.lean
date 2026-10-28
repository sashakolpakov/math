import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback

/-! # Pullback Section Composition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSectionComposition

noncomputable section

/-! Actual section morphisms, not only their nonvanishing loci, respect
the canonical composition comparison for module pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem globalLineSectionPullback_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (M : X.Modules) (s : Γ(M, ⊤)) :
    GlobalSectionComposition.Construction.globalSectionCompositePullback f j M (GlobalSectionCechPullback.Construction.globalLineSectionPullback f M s) =
      GlobalSectionCechPullback.Construction.globalLineSectionPullback (j ≫ f) M s :=
  Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.comp f j M ⊤ ⊤ ⊤ (by simp) (by simp) s

theorem pullbackSection_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (M : X.Modules) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ≫ (Scheme.Modules.pullbackComp j f).hom.app M =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (j ≫ f) s := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (j ≫ f)).obj M)).injective
  rw [GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_composite, GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback, GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback]
  exact globalLineSectionPullback_comp f j M (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSectionComposition
