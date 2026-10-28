import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IteratedGroupPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange

/-! # Arithmetic Product Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticProductPoints.CM

noncomputable section

/-! The point equivalence for the product of geometric Albanese factors
agrees with iterated base change of the original arithmetic product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IteratedGroupPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM

variable {S T : Scheme} {r : ℕ} (A : Fin r → CommGrp (Over S))
  {k : Type} [Field k] (b : T ⟶ S) (c : Spec (.of k) ⟶ T)
  (d : Spec (.of k) ⟶ S) (hd : c ≫ b = d)

def comparisonGroup :
    (GroupBaseChange.CM.changedGroup (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) b) c).toGrp ≅
      (AbelianScheme.TateComparison.Products.componentProduct (ProductBaseChange.CM.changedFactors A d)).toGrp :=
  (GroupBaseChange.CM.factorGroupIso (AbelianScheme.TateComparison.Products.componentProduct A) c b d hd).symm ≪≫ ProductBaseChange.CM.productBaseChangeGroupIso A d

def comparison :
    (GroupBaseChange.CM.changedGroup (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) b) c).X ≅
      (AbelianScheme.TateComparison.Products.componentProduct (ProductBaseChange.CM.changedFactors A d)).X :=
  (Grp.forget _).mapIso (comparisonGroup A b c d hd)

theorem comparison_inv :
    (comparison A b c d hd).inv = (ProductBaseChange.CM.productBaseChangeIso A d).inv ≫
      (IteratedGroupPoints.CM.factorIso (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd).hom := rfl

theorem product_point
    (p : Geometric.PointExt.CM.pointBase k ⟶ (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) d).X) :
    FiberGeneration.CM.fiberPointsEquiv (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) b).X c
      ((p ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom) ≫ (comparison A b c d hd).inv) =
        PrimeFieldPoints.CM.pointEquiv b c d hd (AbelianScheme.TateComparison.Products.componentProduct A).X p := by
  rw [comparison_inv]
  have hcancel : (ProductBaseChange.CM.productBaseChangeIso A d).hom ≫ (ProductBaseChange.CM.productBaseChangeIso A d).inv ≫
      (IteratedGroupPoints.CM.factorIso (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd).hom =
        (IteratedGroupPoints.CM.factorIso (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd).hom :=
    (ProductBaseChange.CM.productBaseChangeIso A d).hom_inv_id_assoc _
  have hpoint : (p ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom) ≫
      (ProductBaseChange.CM.productBaseChangeIso A d).inv ≫ (IteratedGroupPoints.CM.factorIso (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd).hom =
        p ≫ (IteratedGroupPoints.CM.factorIso (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd).hom :=
    (Category.assoc _ _ _).trans (congrArg (p ≫ ·) hcancel)
  exact (congrArg (FiberGeneration.CM.fiberPointsEquiv (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) b).X c) hpoint).trans
    (IteratedGroupPoints.CM.factorIso_points (AbelianScheme.TateComparison.Products.componentProduct A) b c d hd p)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticProductPoints.CM
