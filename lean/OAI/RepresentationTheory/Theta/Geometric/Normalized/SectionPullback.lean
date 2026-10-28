import OAI.RepresentationTheory.Theta.Geometric.RestrictedAxisBaseChange
import OAI.RepresentationTheory.Theta.Geometric.Normalized.ClosedFiberFrames

/-! # Section Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionPullback

noncomputable section

/-! Normalization of an arbitrary section is preserved on the actual
Cartesian family, before any frame condition is imposed. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem globalAxisValue_baseChange {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (a : Γ(M, ⊤)) :
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
      (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M)
        (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback f M a)) =
      g.appTop (r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s M a)) :=
  RestrictedAxisBaseChange.restrictedAxisValue_baseChange f b g s h M r ⊤ ⊤ (by simp) (by simp) (by simp) a

theorem normalizedSection_pullback {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (ha : r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s M (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M a)) =
      (1 : Γ(S, ⊤))) :
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
      (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj M)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f a))) = (1 : Γ(T, ⊤)) := by
  rw [AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_pullback, globalAxisValue_baseChange, ha, map_one]

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionPullback
