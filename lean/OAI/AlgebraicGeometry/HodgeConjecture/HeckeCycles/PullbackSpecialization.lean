import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation

/-! # Pullback Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM

noncomputable section

/-! Proper specialization commutes with the projection from a
base-changed model to its original arithmetic model. The proof uses
the uniqueness of the same valuative extension on both sides. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

variable {S T : Scheme} (t : T ⟶ S) (X : Over S) [IsProper X.hom]
  {R L : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
  (bR : Spec (.of R) ⟶ T)

abbrev localModel := (Over.pullback t).obj X

instance localModel_proper : IsProper (localModel t X).hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom t))

def genericTestMap : ValuativePoints.CM.genericTest (L := L) (bR ≫ t) ⟶ (Over.map t).obj (ValuativePoints.CM.genericTest (L := L) bR) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.assoc _ _ _))

def projectGeneric (z : ValuativePoints.CM.genericTest (L := L) bR ⟶ localModel t X) :
    ValuativePoints.CM.genericTest (L := L) (bR ≫ t) ⟶ X :=
  genericTestMap t bR ≫ BaseChangeEvaluation.CM.pointsEquiv t (ValuativePoints.CM.genericTest bR) X z

def projectIntegral (u : Over.mk bR ⟶ localModel t X) : Over.mk (bR ≫ t) ⟶ X :=
  BaseChangeEvaluation.CM.pointsEquiv t (Over.mk bR) X u

omit [IsProper X.hom] [IsDomain R] [ValuationRing R] [IsFractionRing R L] in
theorem project_restriction (u : Over.mk bR ⟶ localModel t X) :
    projectGeneric t X bR (ValuativePoints.CM.restrictPoint (L := L) bR (localModel t X) u) =
      ValuativePoints.CM.restrictPoint (L := L) (bR ≫ t) X (projectIntegral t X bR u) := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((ValuativePoints.CM.genericBase (R := R) (L := L) ≫ u.left) ≫ pullback.fst X.hom t) =
    ValuativePoints.CM.genericBase (R := R) (L := L) ≫ (u.left ≫ pullback.fst X.hom t)
  exact (Category.id_comp _).trans (Category.assoc _ _ _)

variable {k : Type} [Field k] (res : R →+* k)

def specialTestMap : ValuativePoints.CM.specialTest (bR ≫ t) res ⟶ (Over.map t).obj (ValuativePoints.CM.specialTest bR res) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.assoc _ _ _))

def projectSpecial (z : ValuativePoints.CM.specialTest bR res ⟶ localModel t X) : ValuativePoints.CM.specialTest (bR ≫ t) res ⟶ X :=
  specialTestMap t bR res ≫ BaseChangeEvaluation.CM.pointsEquiv t (ValuativePoints.CM.specialTest bR res) X z

omit [IsProper X.hom] [IsDomain R] [ValuationRing R] in
theorem project_reduction (u : Over.mk bR ⟶ localModel t X) :
    projectSpecial t X bR res (ValuativePoints.CM.reductionTest bR res ≫ u) =
      ValuativePoints.CM.reductionTest (bR ≫ t) res ≫ projectIntegral t X bR u := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ ((Spec.map (CommRingCat.ofHom res) ≫ u.left) ≫ pullback.fst X.hom t) =
    Spec.map (CommRingCat.ofHom res) ≫ (u.left ≫ pullback.fst X.hom t)
  exact (Category.id_comp _).trans (Category.assoc _ _ _)

theorem project_specialization (z : ValuativePoints.CM.genericTest (L := L) bR ⟶ localModel t X) :
    projectSpecial t X bR res (ValuativePoints.CM.specializePoint bR res (localModel t X) z) =
      ValuativePoints.CM.specializePoint (bR ≫ t) res X (projectGeneric t X bR z) := by
  let u := (ValuativePoints.CM.evaluatedPointEquiv bR (localModel t X)).symm z
  have hu : ValuativePoints.CM.restrictPoint (L := L) bR (localModel t X) u = z :=
    (ValuativePoints.CM.evaluatedPointEquiv bR (localModel t X)).apply_symm_apply z
  have hg : ValuativePoints.CM.restrictPoint (L := L) (bR ≫ t) X (projectIntegral t X bR u) =
      projectGeneric t X bR z :=
    (project_restriction t X bR u).symm.trans (congrArg (projectGeneric t X bR) hu)
  have he : (ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X).symm (projectGeneric t X bR z) =
      projectIntegral t X bR u :=
    (congrArg (ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X).symm hg).symm.trans
      ((ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X).symm_apply_apply (projectIntegral t X bR u))
  change projectSpecial t X bR res (ValuativePoints.CM.reductionTest bR res ≫ u) =
    ValuativePoints.CM.reductionTest (bR ≫ t) res ≫ (ValuativePoints.CM.evaluatedPointEquiv (bR ≫ t) X).symm (projectGeneric t X bR z)
  rw [he]
  exact project_reduction t X bR res u

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM
