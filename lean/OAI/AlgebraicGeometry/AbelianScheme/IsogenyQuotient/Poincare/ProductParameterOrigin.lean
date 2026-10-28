import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroProduct

/-! # Product Parameter Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductParameterOrigin.Construction

noncomputable section

/-! Naturality identifies the origin of the Poincare product over
any group parameter with the original common zero-frame product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T]

theorem poincareHorizontalProduct_fiber_origin
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a b c) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a b c 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c) (HorizontalProduct.Construction.poincareHorizontalProduct D a b c h) =
        BilinearProducts.Construction.framedLineProduct (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) :=
  (HorizontalProduct.Construction.poincareHorizontalProduct_natural D η[T] a b c h 1 1 1
    (ZeroProduct.Construction.horizontalOneProductRel D.abelian.scheme A.scheme _) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b)
    (NormalizedProductOrigin.Construction.groupMap_origin c)).trans (ZeroProduct.Construction.poincareHorizontalProduct_at_zero D)

theorem poincareVerticalProduct_fiber_origin
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a b c) :
    Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a b c 1 1 1
      (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin c) (VerticalProduct.Construction.poincareVerticalProduct D a b c h) =
        BilinearProducts.Construction.framedLineProduct (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _) :=
  (VerticalProduct.Construction.poincareVerticalProduct_natural D η[T] a b c h 1 1 1
    (ZeroProduct.Construction.verticalOneProductRel A.scheme D.abelian.scheme _) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b)
    (NormalizedProductOrigin.Construction.groupMap_origin c)).trans (ZeroProduct.Construction.poincareVerticalProduct_at_zero D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductParameterOrigin.Construction
