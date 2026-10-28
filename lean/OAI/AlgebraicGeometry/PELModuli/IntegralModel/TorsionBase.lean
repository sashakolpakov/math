import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantGroupBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Torsion Base -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionBase.TorsionBaseChange

noncomputable section

/-! The actual torsion group scheme commutes with arbitrary base change.
The comparison is constructed from its represented group-valued point
functor and preserves its actual inclusion into the ambient group scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S S' : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) (f : S' ⟶ S)

def pointsMulEquiv (T : Over S') :
    AbelianScheme.TorsionQuotient.Group.TorsionGroup.points ((Over.pullback f).obj A) n T ≃*
      AbelianScheme.TorsionQuotient.Group.TorsionGroup.points A n ((Over.map f).obj T) where
  toFun x := ⟨Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T x.val, by
    change (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T x.val) ^ n = 1
    rw [← map_pow, show x.val ^ n = 1 from x.property, map_one]⟩
  invFun x := ⟨(Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T).symm x.val, by
    change ((Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T).symm x.val) ^ n = 1
    rw [← map_pow, show x.val ^ n = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext ((Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f T).map_mul x.val y.val)

def pointFunctorIso : AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointFunctor ((Over.pullback f).obj A) n ≅
    (Over.map f).op ⋙ AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointFunctor A n :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (pointsMulEquiv A n f T.unop)) (by
    intro T U h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _)

def comparisonIso : yonedaGrpObj (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n) ≅
    yonedaGrpObj ((Over.pullback f).obj (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n)) :=
    AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointIso ((Over.pullback f).obj A) n ≪≫ pointFunctorIso A n f ≪≫
      (Functor.isoWhiskerLeft (Over.map f).op (AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointIso A n)).symm ≪≫
        (ConstantGroupBaseChange.GroupPoints.baseChangeGroupIso (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) f).symm

def groupIso : Grp.mk (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n) ≅
    Grp.mk ((Over.pullback f).obj (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n)) :=
  yonedaGrpFullyFaithful.preimageIso (comparisonIso A n f)

def schemeIso : AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n ≅
    (Over.pullback f).obj (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) :=
  (Grp.forget (Over S')).mapIso (groupIso A n f)

instance schemeIso_isMonHom : IsMonHom (schemeIso A n f).hom :=
  inferInstanceAs (IsMonHom (groupIso A n f).hom.hom.hom)

theorem schemeIso_hom_eval :
    (schemeIso A n f).hom = (comparisonIso A n f).hom.app
      (.op (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n)) (𝟙 _) := by
  have h : yonedaGrp.map (groupIso A n f).hom = (comparisonIso A n f).hom :=
    yonedaGrpFullyFaithful.map_preimage _
  have he := congrArg (fun t => t.app (.op (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n)) (𝟙 _)) h
  exact (Category.id_comp _).symm.trans he

theorem pointIso_inv_inclusion (T : Over S) (x : AbelianScheme.TorsionQuotient.Group.TorsionGroup.points A n T) :
    (AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointIso A n).inv.app (.op T) x ≫ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n = x.val :=
  AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n x.val x.property

theorem baseChangeGroupIso_inv_fst (T : Over S') (x : (Over.map f).obj T ⟶ AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) :
    ((ConstantGroupBaseChange.GroupPoints.baseChangeGroupIso (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) f).inv.app (.op T) x).left ≫
      pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom f = x.left :=
  congrArg Over.Hom.left ((Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) f T).apply_symm_apply x)

theorem schemeIso_fst_inclusion :
    (schemeIso A n f).hom.left ≫ pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom f ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left =
      (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι ((Over.pullback f).obj A) n).left ≫ pullback.fst A.hom f := by
  let T := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback f).obj A) n
  let x₀ := (AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointIso ((Over.pullback f).obj A) n).hom.app (.op T) (𝟙 T)
  let x₁ := (pointFunctorIso A n f).hom.app (.op T) x₀
  let x₂ := (AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointIso A n).inv.app (.op ((Over.map f).obj T)) x₁
  apply Eq.trans (congrArg (fun p => p.left ≫ pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom f ≫
    (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left) (schemeIso_hom_eval A n f))
  change ((ConstantGroupBaseChange.GroupPoints.baseChangeGroupIso (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) f).inv.app (.op T) x₂).left ≫
    pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom f ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left = _
  apply Eq.trans (Category.assoc _ _ _).symm
  apply Eq.trans (congrArg (fun p => p ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left)
    (baseChangeGroupIso_inv_fst A n f T x₂))
  have h := congrArg Over.Hom.left (pointIso_inv_inclusion A n ((Over.map f).obj T) x₁)
  apply Eq.trans h
  change ((𝟙 T.left) ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι ((Over.pullback f).obj A) n).left) ≫ _ = _
  rw [Category.id_comp]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.TorsionBase.TorsionBaseChange
