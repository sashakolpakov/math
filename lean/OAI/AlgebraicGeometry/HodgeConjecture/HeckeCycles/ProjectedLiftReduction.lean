import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction

/-! # Projected Lift Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedLiftReduction.CM

noncomputable section

/-! Specialization of a local point lying over a prescribed arithmetic
lift recovers the original geometric point on the arithmetic model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {S T : Scheme} (t : T ⟶ S) (X : Over S) [IsProper X.hom]
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ T) {k : Type} [Field k]
  (e : k ≃+* IsLocalRing.ResidueField R) (bk : Spec (.of k) ⟶ S)
  (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X)
  (l : LiftMap.CM.SmoothPoint.IntegralLift X R e (bR ≫ t) bk p)

theorem projected_specialization_recovers_lift
    (z : ValuativePoints.CM.genericTest (L := L) bR ⟶ PullbackSpecialization.CM.localModel t X)
    (hz : z.left ≫ pullback.fst X.hom t =
      ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l.map) :
    (ValuativePoints.CM.specializePoint bR (LiftedReduction.CM.geometricResidue e) (PullbackSpecialization.CM.localModel t X) z).left ≫ pullback.fst X.hom t =
      p.left ≫ pullback.fst X.hom bk := by
  have hg : (PullbackSpecialization.CM.projectGeneric t X bR z).left = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l.map := by
    change 𝟙 _ ≫ (z.left ≫ pullback.fst X.hom t) = _
    exact (Category.id_comp _).trans hz
  have hr := LiftedReduction.CM.specialization_recovers_lift X e (bR ≫ t) bk p l (PullbackSpecialization.CM.projectGeneric t X bR z) hg
  have he := congrArg Over.Hom.left (PullbackSpecialization.CM.project_specialization t X bR (LiftedReduction.CM.geometricResidue e) z)
  have h := he.trans hr
  change 𝟙 _ ≫ ((ValuativePoints.CM.specializePoint bR (LiftedReduction.CM.geometricResidue e) (PullbackSpecialization.CM.localModel t X) z).left ≫
    pullback.fst X.hom t) = _ at h
  exact (Category.id_comp _).symm.trans h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedLiftReduction.CM
