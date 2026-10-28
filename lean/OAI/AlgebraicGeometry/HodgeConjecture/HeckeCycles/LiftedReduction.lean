import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap

/-! # Lifted Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM

noncomputable section

/-! Proper specialization of a generic point of a prescribed integral
lift recovers its original geometric reduction. This applies to the
actual Witt lifts and their finite evaluation extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberGeneration.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  {S : Scheme} (X : Over S) [IsProper X.hom]
  {k : Type} [Field k] (e : k ≃+* IsLocalRing.ResidueField R)
  (bR : Spec (.of R) ⟶ S) (bk : Spec (.of k) ⟶ S)
  (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X)
  (l : LiftMap.CM.SmoothPoint.IntegralLift X R e bR bk p)

def geometricResidue : R →+* k := e.symm.toRingHom.comp (IsLocalRing.residue R)

def integralPoint : Over.mk bR ⟶ X := Over.homMk l.map l.overBase

theorem geometricResidue_square :
    e.toRingHom.comp (geometricResidue e) = IsLocalRing.residue R := by
  ext r
  exact e.apply_symm_apply _

omit [IsProper X.hom] in
theorem lift_reduction :
    Spec.map (CommRingCat.ofHom (geometricResidue e)) ≫ l.map =
      p.left ≫ pullback.fst X.hom bk := by
  let f := Spec.map (CommRingCat.ofHom e.toRingHom)
  have hf : IsIso f := by
    change IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  apply (cancel_epi f).mp
  have hc : f ≫ Spec.map (CommRingCat.ofHom (geometricResidue e)) = LiftMap.CM.SmoothPoint.closedBase R := by
    rw [← Spec.map_comp]
    exact congrArg (fun r : R →+* IsLocalRing.ResidueField R => Spec.map (CommRingCat.ofHom r))
      (geometricResidue_square e)
  rw [← Category.assoc, hc]
  exact l.reduction

theorem specialize_restriction :
    ValuativePoints.CM.specializePoint bR (geometricResidue e) X
      (ValuativePoints.CM.restrictPoint (L := L) bR X (integralPoint X e bR bk p l)) =
        ValuativePoints.CM.reductionTest bR (geometricResidue e) ≫ integralPoint X e bR bk p l := by
  change ValuativePoints.CM.reductionTest bR (geometricResidue e) ≫
    (ValuativePoints.CM.evaluatedPointEquiv bR X).symm
      (ValuativePoints.CM.evaluatedPointEquiv bR X (integralPoint X e bR bk p l)) = _
  rw [Equiv.symm_apply_apply]

theorem specialization_recovers_lift
    (z : ValuativePoints.CM.genericTest (L := L) bR ⟶ X)
    (hz : z.left = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l.map) :
    (ValuativePoints.CM.specializePoint bR (geometricResidue e) X z).left =
      p.left ≫ pullback.fst X.hom bk := by
  have hpoint : z = ValuativePoints.CM.restrictPoint (L := L) bR X (integralPoint X e bR bk p l) :=
    Over.OverMorphism.ext hz
  rw [hpoint, specialize_restriction]
  exact lift_reduction X e bR bk p l

theorem fiber_specialization_recovers_lift
    (z : Geometric.PointExt.CM.pointBase L ⟶ (Over.pullback (ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)).obj X)
    (hz : z.left ≫ pullback.fst X.hom (ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR) =
      ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l.map) :
    (ValuativePoints.CM.specializePoint bR (geometricResidue e) X
      (FiberGeneration.CM.fiberPointsEquiv X (ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR) z)).left =
        p.left ≫ pullback.fst X.hom bk := by
  apply specialization_recovers_lift X e bR bk p l
  change (𝟙 _) ≫ (z.left ≫ pullback.fst X.hom _) = _
  exact (Category.id_comp _).trans hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM
