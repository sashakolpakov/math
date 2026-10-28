import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction

/-! # Group Right Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupRightUnits.Construction

noncomputable section

/-! Right-unit identities for the original Poincare products on proper
smooth connected group parameters, proved from origin normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]

theorem poincareHorizontalGroupRightUnit_end
    (x a : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x a x) :
    RightContraction.Construction.lineContractRight (HorizontalProduct.Construction.poincareHorizontalProduct D x a x h) (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) _
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := RightContraction.Construction.lineContractRight_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x a x 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x)
    (HorizontalProduct.Construction.poincareHorizontalProduct D x a x h) (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom
  rw [ProductParameterOrigin.Construction.poincareHorizontalProduct_fiber_origin,
    AxisFrames.Construction.poincareHorizontalUnitFrame_natural D η[T] a 1 ha (MonObj.one_comp (fst D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin a), AxisFrames.Construction.poincareHorizontalUnitFrame_zero] at hp
  exact hp.symm.trans (RightContraction.Construction.lineContractRight_unit _ _
    (FramedProductLaws.Construction.framedLineProduct_unit_right (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)))

theorem poincareHorizontalGroupUnit_right
    (x a : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D x a x h).app U m
      ((AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareHorizontalGroupRightUnit_end D x a ha h))

theorem poincareVerticalGroupRightUnit_end
    (x a : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x a x) :
    RightContraction.Construction.lineContractRight (VerticalProduct.Construction.poincareVerticalProduct D x a x h) (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) _
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := RightContraction.Construction.lineContractRight_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) η[T] x a x 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x)
    (VerticalProduct.Construction.poincareVerticalProduct D x a x h) (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom
  rw [ProductParameterOrigin.Construction.poincareVerticalProduct_fiber_origin,
    VerticalUnits.Construction.poincareVerticalUnitFrame_natural D η[T] a 1 ha (MonObj.one_comp (snd D.abelian.scheme A.scheme))
      (NormalizedProductOrigin.Construction.groupMap_origin a), VerticalUnits.Construction.poincareVerticalUnitFrame_zero] at hp
  exact hp.symm.trans (RightContraction.Construction.lineContractRight_unit _ _
    (FramedProductLaws.Construction.framedLineProduct_unit_right (OriginFrames.Construction.poincareZeroFrame D _) (OriginFrames.Construction.poincareZeroFrame D _)))

theorem poincareVerticalGroupUnit_right
    (x a : T ⟶ D.abelian.scheme ⊗ A.scheme) [IsMonHom x] [IsMonHom a]
    (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D x a x h).app U m
      ((VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareVerticalGroupRightUnit_end D x a ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupRightUnits.Construction
