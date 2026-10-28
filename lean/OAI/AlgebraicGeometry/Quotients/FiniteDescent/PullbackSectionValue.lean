import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing

/-! # Pullback Section Value -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionValue

noncomputable section

/-! Zero pullback of a section morphism implies zero for the canonical
pullback of its value on the whole scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

namespace Construction.PullbackSectionZero

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {M : X.Modules}

theorem value_zero (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (hs : AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s = 0) :
    PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M s) = 0 := by
  have hm : (Scheme.Modules.pullback f).map s = 0 := by
    apply (cancel_epi (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv).mp
    simpa only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, comp_zero] using hs
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s
  change s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map s) at hn
  rw [hm, Functor.map_zero, comp_zero] at hn
  have hv := congrArg (fun a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) =>
      a.app ⊤ (1 : Γ(X, ⊤))) hn
  exact hv

end Construction.PullbackSectionZero

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionValue
