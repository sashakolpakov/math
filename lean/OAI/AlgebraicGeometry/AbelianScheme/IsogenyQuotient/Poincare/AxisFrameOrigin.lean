import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointFrameNormalization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin

/-! # Axis Frame Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrameOrigin.Construction

noncomputable section

/-! The actual Poincare axis frames have the original common zero
normalization when pulled to the origin of any group parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

variable {k : Type} [Field k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {T : Over (Spec (.of k))} [GrpObj T]
  (t : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) [IsMonHom t] [IsMonHom a]

theorem poincareVerticalUnitFrame_point_origin
    (ha : lift t a ≫ snd D.abelian.scheme A.scheme = 1) :
    (Scheme.Modules.pullback η[T].left).mapIso (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t a) ha) =
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso η[T].left ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t a := by
  exact PointFrameNormalization.Construction.atPoint_pullback_of_eq (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t a) ha) η[T] 1 (NormalizedProductOrigin.Construction.groupMap_origin (lift t a)) (OriginFrames.Construction.poincareZeroFrame D _)
    (PointFrameSection.Construction.atPoint_eq_of_pulled_section (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t a) ha) η[T] 1 (NormalizedProductOrigin.Construction.groupMap_origin (lift t a)) (OriginFrames.Construction.poincareZeroFrame D _)
      ((VerticalUnits.Construction.poincareVerticalUnitFrame_natural D η[T] (lift t a) 1 ha
        (MonObj.one_comp (snd D.abelian.scheme A.scheme)) (NormalizedProductOrigin.Construction.groupMap_origin (lift t a))).trans
        (congrArg Iso.hom (VerticalUnits.Construction.poincareVerticalUnitFrame_zero D _))))

theorem poincareHorizontalUnitFrame_point_origin
    (ht : lift t a ≫ fst D.abelian.scheme A.scheme = 1) :
    (Scheme.Modules.pullback η[T].left).mapIso (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift t a) ht) =
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso η[T].left ≪≫ OriginFrames.Construction.poincarePointOriginFrame D t a := by
  exact PointFrameNormalization.Construction.atPoint_pullback_of_eq (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
    (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift t a) ht) η[T] 1 (NormalizedProductOrigin.Construction.groupMap_origin (lift t a)) (OriginFrames.Construction.poincareZeroFrame D _)
    (PointFrameSection.Construction.atPoint_eq_of_pulled_section (lift t a) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (AxisFrames.Construction.poincareHorizontalUnitFrame D (lift t a) ht) η[T] 1 (NormalizedProductOrigin.Construction.groupMap_origin (lift t a)) (OriginFrames.Construction.poincareZeroFrame D _)
      ((AxisFrames.Construction.poincareHorizontalUnitFrame_natural D η[T] (lift t a) 1 ht
        (MonObj.one_comp (fst D.abelian.scheme A.scheme)) (NormalizedProductOrigin.Construction.groupMap_origin (lift t a))).trans
        (congrArg Iso.hom (AxisFrames.Construction.poincareHorizontalUnitFrame_zero D _))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.AxisFrameOrigin.Construction
