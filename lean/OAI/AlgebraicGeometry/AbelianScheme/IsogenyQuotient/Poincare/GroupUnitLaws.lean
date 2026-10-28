import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ProductParameterOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupUnitLaws.Construction

noncomputable section

/-! The original Poincare products satisfy the left unit law on
proper smooth connected group parameters. The law follows from the
common origin normalization and line-endomorphism rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

theorem poincareHorizontalGroupUnit_end
    (a x : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h) (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) _
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := Picard.PoincareBundle.Bilinear.Transport.contractLeft_pullback_transport η[T].left
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x)
    (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
    (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom
  change Picard.PoincareBundle.Bilinear.Contraction.contractLeft
      (Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a x x 1 1 1
        (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin x) (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h))
      (Picard.PoincareBundle.Line.Fibers.pullSection (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a)
        (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom) = _ at hp
  rw [ProductParameterOrigin.Construction.poincareHorizontalProduct_fiber_origin,
    AxisFrames.Construction.poincareHorizontalUnitFrame_natural D η[T] a 1 ha (MonObj.one_comp (fst D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin a), AxisFrames.Construction.poincareHorizontalUnitFrame_zero] at hp
  exact hp.symm.trans (Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit _ _
    (FramedProductLaws.Construction.framedLineProduct_unit_left (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)))

theorem poincareHorizontalGroupUnit_left
    (a x : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h).app U
      ((AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareHorizontalGroupUnit_end D a x ha h))

theorem poincareVerticalGroupUnit_end
    (a x : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (VerticalProduct.Construction.poincareVerticalProduct D a x x h) (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) _
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := Picard.PoincareBundle.Bilinear.Transport.contractLeft_pullback_transport η[T].left
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x)
    (VerticalProduct.Construction.poincareVerticalProduct D a x x h)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom
  change Picard.PoincareBundle.Bilinear.Contraction.contractLeft
      (Picard.PoincareBundle.Line.Fibers.pullBilinear (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a x x 1 1 1
        (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin x) (VerticalProduct.Construction.poincareVerticalProduct D a x x h))
      (Picard.PoincareBundle.Line.Fibers.pullSection (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a)
        (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom) = _ at hp
  rw [ProductParameterOrigin.Construction.poincareVerticalProduct_fiber_origin,
    VerticalUnits.Construction.poincareVerticalUnitFrame_natural D η[T] a 1 ha (MonObj.one_comp (snd D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin a), VerticalUnits.Construction.poincareVerticalUnitFrame_zero] at hp
  exact hp.symm.trans (Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit _ _
    (FramedProductLaws.Construction.framedLineProduct_unit_left (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)))

theorem poincareVerticalGroupUnit_left
    (a x : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom a] [IsMonHom x]
    (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D a x x h).app U
      ((VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareVerticalGroupUnit_end D a x ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupUnitLaws.Construction
