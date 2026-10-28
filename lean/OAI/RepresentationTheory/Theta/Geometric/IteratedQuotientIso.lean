import OAI.RepresentationTheory.Theta.Geometric.QuotientPullback

/-! # Iterated Quotient Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.IteratedQuotientIso

noncomputable section

/-! An actual isomorphism between iterated pullbacks of the primitive
theta line is an isomorphism of the corresponding native projective
quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def iteratedThetaQuotientIso {X Y : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (p : Y ⟶ X) (t : Y ⟶ Y)
    (u : (((AlgebraicQuotient.algebraicThetaQuotient f g).pullback p).pullback t).sheaf ≅
      ((AlgebraicQuotient.algebraicThetaQuotient f g).pullback p).sheaf) :
    (AlgebraicQuotient.algebraicThetaQuotient (t ≫ p ≫ f) (t ≫ p ≫ g)).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (p ≫ f) (p ≫ g)).sheaf :=
  (QuotientPullback.thetaQuotientPullbackIso t (p ≫ f) (p ≫ g)).symm ≪≫
    (Scheme.Modules.pullback t).mapIso (QuotientPullback.thetaQuotientPullbackIso p f g).symm ≪≫
      u ≪≫ QuotientPullback.thetaQuotientPullbackIso p f g

end

end OAI.RepresentationTheory.Theta.Geometric.IteratedQuotientIso
