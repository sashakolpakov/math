import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportHom
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphismOver

/-! # Square Transport Over -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportOver

noncomputable section

/-! The actual square-transported isomorphism agrees with mapped
relation transport in the original slice category. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

theorem lineBundleSquareTransportIso_hom_eq_overPointMorphism {S : Scheme.{0}} {X Y X' Y' : Over S}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (f g : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' g' : Y' ⟶ X')
    (hf : f' ≫ v = r ≫ f) (hg : g' ≫ v = r ≫ g)
    (e : (L.pullback f.left).sheaf ≅ (L.pullback g.left).sheaf) :
    (SquareIsoFrames.lineBundleSquareTransportIso L f.left g.left v.left r.left f'.left g'.left
      (congrArg Over.Hom.left hf) (congrArg Over.Hom.left hg) e).hom =
    PullbackPointMorphism.pullbackPointMorphism (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) v L.sheaf f' g'
      (pullHom e.hom r (f' ≫ v) (g' ≫ v) hf.symm hg.symm) := by
  have h := SquareTransportHom.lineBundleSquareTransportIso_hom_eq_pointMorphism L f.left g.left v.left r.left f'.left g'.left
    (congrArg Over.Hom.left hf) (congrArg Over.Hom.left hg) e
  have hr := Picard.PoincareBundle.DescentReindexing.pullHom_reindex (Over.forget S)
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks e.hom r (f' ≫ v) (g' ≫ v) hf.symm hg.symm
  exact h.trans ((congrArg (PullbackPointMorphism.pullbackPointMorphism Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    v.left L.sheaf f'.left g'.left) hr.symm).trans
      (PullbackPointMorphismOver.pullbackPointMorphism_over v L.sheaf f' g' _).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportOver
