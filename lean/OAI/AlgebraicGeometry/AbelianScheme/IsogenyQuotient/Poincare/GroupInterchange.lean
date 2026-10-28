import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangeOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductParameterOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupInterchange.Construction

noncomputable section

/-! The two original Poincare products satisfy interchange on every
proper smooth connected group parameter, by their common origin frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

theorem poincareGroupProducts_interchange
    (c a b x ca cb ax bx w : T ⟶ D.abelian.scheme ⊗ A.scheme)
    [IsMonHom c] [IsMonHom a] [IsMonHom b] [IsMonHom x] [IsMonHom ca]
    [IsMonHom cb] [IsMonHom ax] [IsMonHom bx] [IsMonHom w]
    (hax : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x ax)
    (hbx : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) b x bx)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) c b cb)
    (hca : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) c a ca)
    (hby : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) cb ax w)
    (haz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) ca bx w)
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) c, U))
    (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a, U)) (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) b, U))
    (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D cb ax w hby).app U ((HorizontalProduct.Construction.poincareHorizontalProduct D c b cb hcb).app U sc sb)
      ((HorizontalProduct.Construction.poincareHorizontalProduct D a x ax hax).app U sa sx) =
    (HorizontalProduct.Construction.poincareHorizontalProduct D ca bx w haz).app U ((VerticalProduct.Construction.poincareVerticalProduct D c a ca hca).app U sc sa)
      ((VerticalProduct.Construction.poincareVerticalProduct D b x bx hbx).app U sb sx) := by
  refine FiberInterchangeOrigin.Construction.fiberBilinear_interchange_of_origin T (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    c a b x ca cb ax bx w 1 1 1 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin c) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin x)
    (NormalizedProductOrigin.Construction.groupMap_origin ca) (NormalizedProductOrigin.Construction.groupMap_origin cb) (NormalizedProductOrigin.Construction.groupMap_origin ax) (NormalizedProductOrigin.Construction.groupMap_origin bx) (NormalizedProductOrigin.Construction.groupMap_origin w)
    (HorizontalProduct.Construction.poincareHorizontalProduct D a x ax hax) (VerticalProduct.Construction.poincareVerticalProduct D b x bx hbx)
    (HorizontalProduct.Construction.poincareHorizontalProduct D c b cb hcb) (VerticalProduct.Construction.poincareVerticalProduct D c a ca hca)
    (VerticalProduct.Construction.poincareVerticalProduct D cb ax w hby) (HorizontalProduct.Construction.poincareHorizontalProduct D ca bx w haz) ?_ U sc sa sb sx
  intro V c a b x
  simp only [ProductParameterOrigin.Construction.poincareHorizontalProduct_fiber_origin, ProductParameterOrigin.Construction.poincareVerticalProduct_fiber_origin]
  exact FramedProductLaws.Construction.framedLineProduct_interchange (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)
    (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)
    (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) V c a b x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupInterchange.Construction
