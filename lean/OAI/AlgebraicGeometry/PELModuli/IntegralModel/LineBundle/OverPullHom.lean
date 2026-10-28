import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.PullHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

/-! # Over Pull Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.OverPullHom

noncomputable section

/-! The native restriction comparison also holds on schemes over a
fixed base, with their literal underlying module pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

theorem lineBundleRestrictIso_hom_eq_overPullHom {S : Scheme.{0}} {X Y Z : Over S}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (f g : Y ⟶ X) (r : Z ⟶ Y) (f' g' : Z ⟶ X)
    (hf : r ≫ f = f') (hg : r ≫ g = g')
    (e : (L.pullback f.left).sheaf ≅ (L.pullback g.left).sheaf) :
    (NormalizedRestriction.lineBundleRestrictIso L f.left g.left r.left f'.left g'.left
      (congrArg Over.Hom.left hf) (congrArg Over.Hom.left hg) e).hom =
      pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) e.hom r f' g' hf hg := by
  rw [PullHom.lineBundleRestrictIso_hom_eq_pullHom]
  exact (Picard.PoincareBundle.DescentReindexing.pullHom_reindex (Over.forget S)
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks e.hom r f' g' hf hg).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.OverPullHom
