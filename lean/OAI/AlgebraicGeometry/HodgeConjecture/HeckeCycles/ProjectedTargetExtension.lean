import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization

/-! # Projected Target Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedTargetExtension.CM

noncomputable section

/-! The proper reduction of a transported generic target has the
projection of its independently specified integral extension. Only the
actual generic map and arithmetic base equations are used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM

variable {S T : Scheme} (t : T ⟶ S) (X : Over S) [IsProper X.hom]
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ T) {k : Type} [Field k] (res : R →+* k)
  (u : ValuativePoints.CM.genericTest (L := L) bR ⟶ PullbackSpecialization.CM.localModel t X)
  (l : Spec (.of R) ⟶ X.left) (hl : l ≫ X.hom = bR ≫ t)
  (hu : u.left ≫ pullback.fst X.hom t = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l)

include hl hu in
theorem specialization_projection :
    (ValuativePoints.CM.specializePoint bR res (PullbackSpecialization.CM.localModel t X) u).left ≫ pullback.fst X.hom t =
      Spec.map (CommRingCat.ofHom res) ≫ l := by
  let ll : Over.mk (bR ≫ t) ⟶ X := Over.homMk l hl
  have hg : PullbackSpecialization.CM.projectGeneric t X bR u = ValuativePoints.CM.restrictPoint (L := L) (bR ≫ t) X ll := by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ (u.left ≫ pullback.fst X.hom t) = ValuativePoints.CM.genericBase (R := R) (L := L) ≫ l
    exact (Category.id_comp _).trans hu
  have hs := PullbackSpecialization.CM.project_specialization t X bR res u
  rw [hg] at hs
  have hr : ValuativePoints.CM.specializePoint (bR ≫ t) res X (ValuativePoints.CM.restrictPoint (L := L) (bR ≫ t) X ll) =
      ValuativePoints.CM.reductionTest (bR ≫ t) res ≫ ll := by
    change ValuativePoints.CM.reductionTest (bR ≫ t) res ≫
      (ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X).symm ((ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X) ll) = _
    rw [Equiv.symm_apply_apply]
  have he := congrArg (fun v => v.left) (hs.trans hr)
  change 𝟙 _ ≫ ((ValuativePoints.CM.specializePoint bR res (PullbackSpecialization.CM.localModel t X) u).left ≫ pullback.fst X.hom t) =
    Spec.map (CommRingCat.ofHom res) ≫ l at he
  exact (Category.id_comp _).symm.trans he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedTargetExtension.CM
