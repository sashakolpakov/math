import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductParameterOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Associativity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupAssociativity.Construction

noncomputable section

/-! The original Poincare products are associative on every proper
smooth connected group parameter. Their common origin normalization
proves the equation by trilinear rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

theorem poincareHorizontalGroupProduct_associative
    (x y z xy yz w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    [IsMonHom x] [IsMonHom y] [IsMonHom z] [IsMonHom xy] [IsMonHom yz] [IsMonHom w]
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) z, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D x yz w hxw).app U m ((HorizontalProduct.Construction.poincareHorizontalProduct D y z yz hyz).app U n p) =
      (HorizontalProduct.Construction.poincareHorizontalProduct D xy z w hzw).app U ((HorizontalProduct.Construction.poincareHorizontalProduct D x y xy hxy).app U m n) p := by
  refine FiberAssociativity.Construction.fiberBilinear_associative_of_origin T (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x y z xy yz w 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin y) (NormalizedProductOrigin.Construction.groupMap_origin z)
    (NormalizedProductOrigin.Construction.groupMap_origin xy) (NormalizedProductOrigin.Construction.groupMap_origin yz) (NormalizedProductOrigin.Construction.groupMap_origin w)
    (HorizontalProduct.Construction.poincareHorizontalProduct D y z yz hyz) (HorizontalProduct.Construction.poincareHorizontalProduct D x yz w hxw)
    (HorizontalProduct.Construction.poincareHorizontalProduct D x y xy hxy) (HorizontalProduct.Construction.poincareHorizontalProduct D xy z w hzw) ?_ U m n p
  intro V a b c
  simp only [ProductParameterOrigin.Construction.poincareHorizontalProduct_fiber_origin]
  exact FramedProductLaws.Construction.framedLineProduct_associative (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)
    (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) V a b c

theorem poincareVerticalGroupProduct_associative
    (x y z xy yz w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    [IsMonHom x] [IsMonHom y] [IsMonHom z] [IsMonHom xy] [IsMonHom yz] [IsMonHom w]
    (hxy : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x y xy)
    (hyz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) y z yz)
    (hxw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x yz w)
    (hzw : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) xy z w)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U))
    (n : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) y, U)) (p : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) z, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D x yz w hxw).app U m ((VerticalProduct.Construction.poincareVerticalProduct D y z yz hyz).app U n p) =
      (VerticalProduct.Construction.poincareVerticalProduct D xy z w hzw).app U ((VerticalProduct.Construction.poincareVerticalProduct D x y xy hxy).app U m n) p := by
  refine FiberAssociativity.Construction.fiberBilinear_associative_of_origin T (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x y z xy yz w 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin y) (NormalizedProductOrigin.Construction.groupMap_origin z)
    (NormalizedProductOrigin.Construction.groupMap_origin xy) (NormalizedProductOrigin.Construction.groupMap_origin yz) (NormalizedProductOrigin.Construction.groupMap_origin w)
    (VerticalProduct.Construction.poincareVerticalProduct D y z yz hyz) (VerticalProduct.Construction.poincareVerticalProduct D x yz w hxw)
    (VerticalProduct.Construction.poincareVerticalProduct D x y xy hxy) (VerticalProduct.Construction.poincareVerticalProduct D xy z w hzw) ?_ U m n p
  intro V a b c
  simp only [ProductParameterOrigin.Construction.poincareVerticalProduct_fiber_origin]
  exact FramedProductLaws.Construction.framedLineProduct_associative (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)
    (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) V a b c

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupAssociativity.Construction
