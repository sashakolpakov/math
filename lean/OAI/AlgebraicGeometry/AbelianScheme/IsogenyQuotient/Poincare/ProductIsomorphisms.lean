import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

/-! # Product Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductIsomorphisms.Construction

noncomputable section

/-!
Actual tensor-product isomorphisms for the original Poincare bundle.
These are constructed from its represented Picard addition. The unique
normalization at the origin will fix the products used in PoincareBundle; the unit,
associativity and interchange laws must still be checked for those products.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem lineBundle_isPoincareBundleLine {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Picard.PoincareBundle.Line.Bundles.IsLine L.sheaf :=
  L.locallyTrivial

def lineTensorFrameComparison {X Y : Scheme.{u}} (p : X ⟶ Y)
    (L M N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (L.pullback p).sheaf)
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (M.pullback p).sheaf)
    (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ (N.pullback p).sheaf) :
    ((L.tensor M).pullback p).sheaf ≅ (N.pullback p).sheaf :=
  Picard.PoincareBundle.Tensor.LinePullback.pullbackIso p L.sheaf M.sheaf (lineBundle_isPoincareBundleLine L) (lineBundle_isPoincareBundleLine M) ≪≫
    Picard.PoincareBundle.Tensor.UnitPullback.tensorIso l.symm m.symm ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≪≫ n

theorem origin_appTop_isIso
    {k : Type u} [Field k] (T : Over (Spec (.of k))) [GrpObj T]
    [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom] :
    IsIso η[T].left.appTop := by
  have : IsIso T.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso T
  have h : IsIso (T.hom.appTop ≫ η[T].left.appTop) := by
    rw [← Scheme.Hom.comp_appTop, Over.w]
    change IsIso (Scheme.Hom.appTop (𝟙 (Spec (.of k))))
    rw [Scheme.Hom.id_appTop]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))}

def poincarePointLine (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left :=
  D.poincare.pullback (lift t a).left

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem poincarePointLine_tensor_left (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (poincarePointLine D t a).sheaf (poincarePointLine D v a).sheaf ≅
      (poincarePointLine D (t * v) a).sheaf) :=
  Quotient.exact (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_mul_left D t v a).symm

theorem poincarePointLine_tensor_right (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme) :
    Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (poincarePointLine D t a).sheaf (poincarePointLine D t b).sheaf ≅
      (poincarePointLine D t (a * b)).sheaf) :=
  Quotient.exact (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_mul_right D t a b).symm

variable [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

/-- Prescribing the original line frames at the origin selects one actual horizontal product isomorphism. -/
theorem existsUnique_normalizedPoincareProduct_left
    (t v : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme)
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D t a).pullback η[T].left).sheaf)
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D v a).pullback η[T].left).sheaf)
    (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D (t * v) a).pullback η[T].left).sheaf) :
    ∃! e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (poincarePointLine D t a).sheaf (poincarePointLine D v a).sheaf ≅
        (poincarePointLine D (t * v) a).sheaf,
      (Scheme.Modules.pullback η[T].left).mapIso e =
        lineTensorFrameComparison η[T].left _ _ _ l m n := by
  have : IsIso η[T].left.appTop := origin_appTop_isIso T
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[T].left
    ((poincarePointLine D t a).tensor (poincarePointLine D v a)) (poincarePointLine D (t * v) a)
    (Classical.choice (poincarePointLine_tensor_left D t v a))
    (lineTensorFrameComparison η[T].left _ _ _ l m n)

/-- The vertical product is likewise determined by the original line frames at the origin. -/
theorem existsUnique_normalizedPoincareProduct_right
    (t : T ⟶ D.abelian.scheme) (a b : T ⟶ A.scheme)
    (l : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D t a).pullback η[T].left).sheaf)
    (m : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D t b).pullback η[T].left).sheaf)
    (n : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
      ((poincarePointLine D t (a * b)).pullback η[T].left).sheaf) :
    ∃! e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (poincarePointLine D t a).sheaf (poincarePointLine D t b).sheaf ≅
        (poincarePointLine D t (a * b)).sheaf,
      (Scheme.Modules.pullback η[T].left).mapIso e =
        lineTensorFrameComparison η[T].left _ _ _ l m n := by
  have : IsIso η[T].left.appTop := origin_appTop_isIso T
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso η[T].left
    ((poincarePointLine D t a).tensor (poincarePointLine D t b)) (poincarePointLine D t (a * b))
    (Classical.choice (poincarePointLine_tensor_right D t a b))
    (lineTensorFrameComparison η[T].left _ _ _ l m n)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductIsomorphisms.Construction
