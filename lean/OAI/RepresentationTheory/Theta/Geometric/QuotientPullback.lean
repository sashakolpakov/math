import OAI.RepresentationTheory.Theta.Geometric.AlgebraicQuotient
import OAI.RepresentationTheory.Theta.Geometric.TensorModulePullback

/-! # Quotient Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientPullback

noncomputable section

/-! Pullback of the actual consecutive hyperplane quotient is the
quotient of the two composed projective maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def thetaQuotientPullbackIso {X Y : Scheme} (t : X ⟶ Y) {n m : ℕ}
    (f : Y ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : Y ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    ((AlgebraicQuotient.algebraicThetaQuotient f g).pullback t).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f) (t ≫ g)).sheaf :=
  TensorModulePullback.tensorModulePullbackIso t
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (AlgebraicQuotient.algebraicTwistBundle m 1)).sheaf
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n (-1))).sheaf ≪≫
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
        ((Scheme.Modules.pullbackComp t g).app (AlgebraicQuotient.algebraicTwistBundle m 1).sheaf)
        ((Scheme.Modules.pullbackComp t f).app (AlgebraicQuotient.algebraicTwistBundle n (-1)).sheaf)

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientPullback
