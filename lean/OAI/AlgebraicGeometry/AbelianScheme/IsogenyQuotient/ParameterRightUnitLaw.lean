import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupParameterUnitLaw
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction

/-! # Parameter Right Unit Law -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterRightUnitLaw.Construction

noncomputable section

/-! The right unit law follows by rigidity from the common zero-frame
normalization of an actual bilinear product and its unit frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

universe u
variable {k : Type u} [Field k] {T E : Over (Spec (.of k))} [GrpObj T] [GrpObj E]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (x a : T ⟶ E) [IsMonHom x] [IsMonHom a]
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x))
  (unit : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L a)
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Picard.PoincareBundle.Line.Fibers.fiber L (1 : 𝟙_ (Over (Spec (.of k))) ⟶ E))

theorem groupParameter_rightUnit_of_origin
    (hβ : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] x a x 1 1 1 (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) β =
      Poincare.BilinearProducts.Construction.framedLineProduct z z z)
    (hu : Picard.PoincareBundle.Line.Fibers.pullSection L η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a) unit.hom = z.hom) :
    RightContraction.Construction.lineContractRight β unit.hom = 𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine L x) _ (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := RightContraction.Construction.lineContractRight_pullback L η[T] x a x 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) β unit.hom
  rw [hβ, hu] at hp
  exact hp.symm.trans (RightContraction.Construction.lineContractRight_unit _ _ (FramedProductLaws.Construction.framedLineProduct_unit_right z z))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterRightUnitLaw.Construction
