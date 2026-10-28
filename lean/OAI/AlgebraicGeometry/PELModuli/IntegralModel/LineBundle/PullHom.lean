import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.NormalizedRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-! # Pull Hom -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.PullHom

noncomputable section

/-! The concrete native restriction used by the Poincare normalization
is the ordinary pullback morphism in the module pseudofunctor. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

theorem lineBundleRestrictIso_hom_eq_pullHom {X Y Z : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (r : Z ⟶ Y) (f' g' : Z ⟶ X)
    (hf : r ≫ f = f') (hg : r ≫ g = g')
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    (NormalizedRestriction.lineBundleRestrictIso L f g r f' g' hf hg e).hom =
      pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) e.hom r f' g' hf hg := by
  subst f'
  subst g'
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.PullHom
