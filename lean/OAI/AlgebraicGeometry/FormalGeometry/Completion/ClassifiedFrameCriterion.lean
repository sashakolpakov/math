import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClassifiedSectionPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalFrameScheme

/-! # Classified Frame Criterion -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! A global section is a frame exactly when its actual classifying
morphism lands in the universal frame open. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem ClassifiedFrameCriterion.Construction.sectionValue_isFrame_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(M, ⊤)) :
    IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv N).symm (e.hom.app ⊤ s)) ↔
      IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s) := by
  have he : (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv N).symm (e.hom.app ⊤ s) =
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s ≫ e.hom := by
    apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv N).injective
    rw [Equiv.apply_symm_apply]
    change e.hom.app ⊤ s = e.hom.app ⊤ (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s))
    exact congrArg (e.hom.app ⊤) ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).apply_symm_apply s).symm
  rw [he]
  exact isIso_comp_right_iff _ _

variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
  (hp : IsPullback f ρ π g)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.classifiedSectionPullback_isFrame_iff (p : Over.mk g ⟶ D.scheme) :
    IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm
      (D.classifiedSectionPullback f ρ g hp p)) ↔ ∀ y : T, p.left y ∈ D.frameOpen :=
  (ClassifiedFrameCriterion.Construction.sectionValue_isFrame_iso ((Scheme.Modules.pullbackCongr (D.classifierFamilyMap_fst f ρ g hp p)).app L.sheaf)
    (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) (D.classifierFamilyMap f ρ g hp p)
      L.sheaf D.universalSection)).trans
    (D.universalCompositeSection_isIso_iff (D.classifierFamilyMap f ρ g hp p) ρ p.left
      (D.classifierFamilyMap_isPullback f ρ g hp p))

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.section_isFrame_iff_classifier_mem [IsAffine T]
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj L.sheaf)).obj (op ⊤)) :
    IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm s) ↔
      ∀ y : T, (D.sectionPointEquiv f ρ g hp s).left y ∈ D.frameOpen := by
  have he := D.classifiedSectionPullback_isFrame_iff f ρ g hp (D.sectionPointEquiv f ρ g hp s)
  rw [D.classifiedSectionPullback_recovers f ρ g hp s] at he
  exact he

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
