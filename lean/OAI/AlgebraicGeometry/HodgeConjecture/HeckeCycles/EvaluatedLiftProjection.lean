import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PointProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedNeighborSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedLiftReduction

/-! # Evaluated Lift Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedLiftProjection.CM

noncomputable section

/-! A generic point of the prescribed arithmetic lift is transported
through the actual source square and evaluated locally. Its proper
specialization recovers that same original geometric point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PointProjection.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {S T U V : Scheme} (d : V ⟶ T) (e : V ⟶ U) (b : T ⟶ S) (c : U ⟶ S)
  (w : d ≫ b = e ≫ c) (X : Over S)
  {R L : Type} [CommRing R] [Field L] [Algebra R L]
  (bR : Spec (.of R) ⟶ T) (cL : Spec (.of L) ⟶ V)
  (wL : cL ≫ d = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ bR)

def evaluatedLocalPoint (z : (Over.map e).obj (Over.mk cL) ⟶ Source.PointProjection.CM.genericSource c X) :
    ValuativePoints.CM.genericTest (L := L) bR ⟶ PullbackSpecialization.CM.localModel b X :=
  EvaluatedNeighborSpecialization.CM.evaluatedPoint d bR cL wL (PullbackSpecialization.CM.localModel b X)
    (Source.PointProjection.CM.localPoint d e b c w X (Over.mk cL) z)

theorem arithmetic_projection (z : (Over.map e).obj (Over.mk cL) ⟶ Source.PointProjection.CM.genericSource c X) :
    (evaluatedLocalPoint d e b c w X bR cL wL z).left ≫ pullback.fst X.hom b =
      z.left ≫ pullback.fst X.hom c := by
  change (𝟙 _ ≫ ((Source.PointProjection.CM.localPoint d e b c w X (Over.mk cL) z).left ≫
    pullback.fst (pullback.snd X.hom b) d)) ≫ pullback.fst X.hom b = _
  simp only [Category.id_comp, Category.assoc]
  exact Source.PointProjection.CM.local_projection d e b c w X (Over.mk cL) z

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] [IsProper X.hom]
  {k : Type} [Field k] (ρ : k ≃+* IsLocalRing.ResidueField R)
  (bk : Spec (.of k) ⟶ S) (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback bk).obj X)
  (l : LiftMap.CM.SmoothPoint.IntegralLift X R ρ (bR ≫ b) bk p)

theorem evaluated_specialization_recovers_lift
    (z : (Over.map e).obj (Over.mk cL) ⟶ Source.PointProjection.CM.genericSource c X)
    (hz : z.left ≫ pullback.fst X.hom c = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l.map) :
    (ValuativePoints.CM.specializePoint bR (LiftedReduction.CM.geometricResidue ρ) (PullbackSpecialization.CM.localModel b X)
      (evaluatedLocalPoint d e b c w X bR cL wL z)).left ≫ pullback.fst X.hom b =
        p.left ≫ pullback.fst X.hom bk :=
  ProjectedLiftReduction.CM.projected_specialization_recovers_lift b X bR ρ bk p l
    (evaluatedLocalPoint d e b c w X bR cL wL z)
    ((arithmetic_projection d e b c w X bR cL wL z).trans hz)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedLiftProjection.CM
