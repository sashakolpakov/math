import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Global Section Hom Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback

noncomputable section

/-! The equivalence between global values and module-sheaf sections
commutes with actual pullback and with its composition isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

theorem globalLineSectionPullback_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) :
    GlobalSectionCechPullback.Construction.globalLineSectionPullback f M s = Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ s :=
  Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.full f M ⊤ s

theorem moduleSectionHomEquiv_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj M) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) =
      GlobalSectionCechPullback.Construction.globalLineSectionPullback f M (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) := by
  let e := AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  have hu : e.hom.app ⊤ (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⊤ (1 : Γ(X, ⊤))) =
      (1 : Γ(Y, ⊤)) := (Quotients.FiniteDescent.StructurePullback.Construction.StructurePullbackValues.apply f ⊤ 1).trans (f.app ⊤).hom.map_one
  have hi : e.inv.app ⊤ (e.hom.app ⊤
      (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⊤ (1 : Γ(X, ⊤)))) =
      Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⊤ (1 : Γ(X, ⊤)) :=
    congrArg (fun a : (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⟶
      (Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) =>
      a.app ⊤ (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⊤ (1 : Γ(X, ⊤)))) e.hom_inv_id
  have he := (congrArg (e.inv.app ⊤) hu).symm.trans hi
  rw [globalLineSectionPullback_eq]
  change ((Scheme.Modules.pullback f).map s).app ⊤ (e.inv.app ⊤ (1 : Γ(Y, ⊤))) =
    Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ (s.app ⊤ (1 : Γ(X, ⊤)))
  exact (congrArg (((Scheme.Modules.pullback f).map s).app ⊤) he).trans
    (Quotients.FiniteDescent.PullbackSectionRestrict.Construction.PullbackSectionCoefficients.naturality f s ⊤ (1 : Γ(X, ⊤))).symm

theorem moduleSectionHomEquiv_composite {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y)
    (M : X.Modules) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (j ≫ f)).obj M)
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j s ≫ (Scheme.Modules.pullbackComp j f).hom.app M) =
    GlobalSectionComposition.Construction.globalSectionCompositePullback f j M (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj M) s) := by
  change ((Scheme.Modules.pullbackComp j f).hom.app M).app ⊤
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback f).obj M))
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j s)) = _
  rw [moduleSectionHomEquiv_pullback]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback
