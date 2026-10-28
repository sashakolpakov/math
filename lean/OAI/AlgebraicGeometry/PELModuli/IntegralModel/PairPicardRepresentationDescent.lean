import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafRepresentationDescent

/-! # Pair Picard Representation Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardRepresentationDescent

noncomputable section

/-! The concrete Poincare class represents the homogeneous Picard sheaf
when the actual local representation has its restricted universal class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem pairPicard_isRepresentedBy {S T : Scheme.{u}} {g : ℕ}
    (A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : T ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.scheme ⊗ A.scheme).left)
    (h : A.IsHomogeneousPicardClass D.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    (h' : (A.pullback b).IsHomogeneousPicardClass (D.pullback b).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme))))
    (R : (A.pullback b).homogeneousPicardSheaf.obj.RepresentableBy (D.pullback b).scheme)
    (hR : R.homEquiv (𝟙 (D.pullback b).scheme) =
      PairPoincareClass.pairPoincareClass (A.pullback b) (D.pullback b)
        (L.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.scheme A.scheme)) h') :
    A.homogeneousPicardSheaf.obj.IsRepresentedBy (PairPoincareClass.pairPoincareClass A D L h) := by
  let R' := R.ofIso ((sheafToPresheaf (Scheme.fppfTopology.over T) (Type (u + 1))).mapIso
    (A.homogeneousPicardSheafBaseChangeIso b))
  apply SheafRepresentationDescent.sheaf_isRepresentedBy_of_fppf_restriction b D.scheme A.homogeneousPicardSheaf
    (PairPoincareClass.pairPoincareClass A D L h) R'
  change A.homogeneousPicardBaseChangeEquiv b (D.pullback b).scheme
    (R.homEquiv (𝟙 (D.pullback b).scheme)) = _
  rw [hR, PairPoincareClass.pairPoincareClass_baseChange A D L h b h', PairPoincareClass.baseChangeProjection_eq_counit D b]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPicardRepresentationDescent
