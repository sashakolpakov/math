import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEndRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin

/-! # Group Parameter Unit Law -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupParameterUnitLaw.Construction

noncomputable section

/-! A bilinear product and its unit frame satisfy the left unit law on a
proper group parameter when both recover the same framed product at zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

universe u
variable {k : Type u} [Field k] {T E : Over (Spec (.of k))} [GrpObj T] [GrpObj E]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (a x : T ⟶ E) [IsMonHom a] [IsMonHom x]
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L x))
  (unit : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber L a)
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Picard.PoincareBundle.Line.Fibers.fiber L (1 : 𝟙_ (Over (Spec (.of k))) ⟶ E))

theorem groupParameter_leftUnit_of_origin
    (hβ : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a x x 1 1 1 (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin x) β =
      Poincare.BilinearProducts.Construction.framedLineProduct z z z)
    (hu : Picard.PoincareBundle.Line.Fibers.pullSection L η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a) unit.hom = z.hom) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft β unit.hom = 𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x) := by
  apply LineEndRigidity.Construction.lineEnd_eq_id_of_origin T (FiberBilinearRigidity.Construction.nativeFiberLine L x) _ (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
  have hp := Picard.PoincareBundle.Bilinear.Transport.contractLeft_pullback_transport η[T].left
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) β
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x 1 (NormalizedProductOrigin.Construction.groupMap_origin x)) unit.hom
  change Picard.PoincareBundle.Bilinear.Contraction.contractLeft
    (Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a x x 1 1 1 (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin x) β)
    (Picard.PoincareBundle.Line.Fibers.pullSection L η[T] a 1 (NormalizedProductOrigin.Construction.groupMap_origin a) unit.hom) = _ at hp
  rw [hβ, hu] at hp
  exact hp.symm.trans (Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit _ _ (FramedProductLaws.Construction.framedLineProduct_unit_left z z))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupParameterUnitLaw.Construction
