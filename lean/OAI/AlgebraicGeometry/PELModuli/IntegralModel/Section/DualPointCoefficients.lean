import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.RelativeLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualNumberReduction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients

/-! # Dual Point Coefficients -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.DualPointCoefficients

noncomputable section

/-! The coordinate-ring map of the actual zero dual-number point
is the constant dual-number lift of the specified field-valued section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem section_dualPoint_coefficients {X Y : Scheme.{0}} (s : X ⟶ Y)
    {k : Type} [Field k] (q : Spec (.of k) ⟶ X) :
    Affine.StalkLifts.AffineStalkLifts.globalMap (Scheme.stalkClosedPointTo (DualNumberReduction.AlgebraicLie.dualBase k ≫ q ≫ s)) =
      (algebraMap k (DualNumber k)).comp
        ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).comp s.appTop.hom) := by
  refine (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap_stalk (DualNumberReduction.AlgebraicLie.dualBase k ≫ q ≫ s)).symm.trans ?_
  apply RingHom.ext
  intro b
  change (Scheme.ΓSpecIso (.of (DualNumber k))).hom
    ((DualNumberReduction.AlgebraicLie.dualBase k ≫ q ≫ s).appTop b) =
      algebraMap k (DualNumber k)
        ((Scheme.ΓSpecIso (.of k)).hom (q.appTop (s.appTop b)))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (q.appTop (s.appTop b))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.DualPointCoefficients
