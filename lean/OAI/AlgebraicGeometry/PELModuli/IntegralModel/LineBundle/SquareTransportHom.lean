import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.PullHom
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphism

/-! # Square Transport Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportHom

noncomputable section

/-! The concrete transported line isomorphism has exactly the
pullback-point formula used by ordinary mapped-relation descent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

theorem lineBundleSquareTransportIso_hom {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' g' : Y' ⟶ X')
    (hf : f' ≫ v = r ≫ f) (hg : g' ≫ v = r ≫ g)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    (SquareIsoFrames.lineBundleSquareTransportIso L f g v r f' g' hf hg e).hom =
      (Scheme.Modules.pullbackComp f' v).hom.app L.sheaf ≫
        (NormalizedRestriction.lineBundleRestrictIso L f g r (f' ≫ v) (g' ≫ v) hf.symm hg.symm e).hom ≫
          (Scheme.Modules.pullbackComp g' v).inv.app L.sheaf := by
  simp only [SquareIsoFrames.lineBundleSquareTransportIso, SquareIsoFrames.lineBundleCommutingSquareIso, NormalizedRestriction.lineBundlePullbackComparison,
    NormalizedRestriction.lineBundleRestrictIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom,
    RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.assoc]
  rfl

theorem lineBundleSquareTransportIso_hom_eq_pointMorphism {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' g' : Y' ⟶ X')
    (hf : f' ≫ v = r ≫ f) (hg : g' ≫ v = r ≫ g)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    (SquareIsoFrames.lineBundleSquareTransportIso L f g v r f' g' hf hg e).hom =
      PullbackPointMorphism.pullbackPointMorphism Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks v L.sheaf f' g'
        (pullHom e.hom r (f' ≫ v) (g' ≫ v) hf.symm hg.symm) := by
  rw [lineBundleSquareTransportIso_hom, PullHom.lineBundleRestrictIso_hom_eq_pullHom]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareTransportHom
