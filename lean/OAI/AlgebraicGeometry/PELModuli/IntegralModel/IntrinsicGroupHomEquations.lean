import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluationCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGroupPoints

/-! # Intrinsic Group Hom Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomEquations.GroupHomEquations

noncomputable section

/-! The closed group equations classify precisely the native relative
group-scheme endomorphisms, on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (G : Over S) [GrpObj G] (T : Over S)

def parameterSourceIso (W : Over S) (b : W ⟶ T) :
    (Over.map T.hom).obj (Over.mk b.left) ≅ W :=
  Over.isoMk (Iso.refl W.left) (by
    change 𝟙 W.left ≫ W.hom = b.left ≫ T.hom
    exact (Category.id_comp W.hom).trans b.w.symm)

def parameterPointsMulEquiv (W : Over S) (b : W ⟶ T) :
    (Over.mk b.left ⟶ (Over.pullback T.hom).obj G) ≃* (W ⟶ G) :=
  (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom (Over.mk b.left)).trans
    (FieldGroupPoints.homDomainMulEquiv (parameterSourceIso T W b).symm G)

theorem parameterPointsMulEquiv_left (W : Over S) (b : W ⟶ T)
    (x : Over.mk b.left ⟶ (Over.pullback T.hom).obj G) :
    (parameterPointsMulEquiv G T W b x).left = x.left ≫ pullback.fst G.hom T.hom := by
  change 𝟙 W.left ≫ (x.left ≫ pullback.fst G.hom T.hom) = _
  exact Category.id_comp _

theorem parameter_point_pair (W : Over S) (b : W ⟶ T)
    (x : Over.mk b.left ⟶ (Over.pullback T.hom).obj G) :
    (prod.lift b (parameterPointsMulEquiv G T W b x)).left ≫
      (IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso G T).hom = x.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_fst,
      ← Over.comp_left, prod.lift_snd, parameterPointsMulEquiv_left]
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_snd,
      ← Over.comp_left, prod.lift_fst]
    exact x.w.symm

theorem native_parameter_evaluation
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G)
    (W : Over S) (b : W ⟶ T) (x : Over.mk b.left ⟶ (Over.pullback T.hom).obj G) :
    parameterPointsMulEquiv G T W b (x ≫ r) =
      prod.lift b (parameterPointsMulEquiv G T W b x) ≫
        IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r := by
  apply Over.OverMorphism.ext
  rw [parameterPointsMulEquiv_left]
  simp only [Over.comp_left]
  rw [IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv_left,
    ← Category.assoc, ← Category.assoc, parameter_point_pair]

def nativeEvaluationHom
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G) [IsMonHom r]
    (W : Over S) (b : W ⟶ T) : (W ⟶ G) →* (W ⟶ G) :=
  let e := parameterPointsMulEquiv G T W b
  e.toMonoidHom.comp ((IsMonHom.monoidHom r (Over.mk b.left)).comp e.symm.toMonoidHom)

theorem nativeEvaluationHom_apply
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G) [IsMonHom r]
    (W : Over S) (b : W ⟶ T) (x : W ⟶ G) :
    nativeEvaluationHom G T r W b x =
      prod.lift b x ≫ IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r := by
  let e := parameterPointsMulEquiv G T W b
  change parameterPointsMulEquiv G T W b (e.symm x ≫ r) = _
  rw [native_parameter_evaluation]
  rw [e.apply_symm_apply]

theorem native_group_equations_of_isMonHom
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G) [IsMonHom r] :
    Group.HomEquations.GroupHomEquations.RespectsGroup G (IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r) := by
  apply Group.HomEvaluationCriterion.GroupHomEquations.respectsGroup_of_evaluation
  · intro W b
    rw [← nativeEvaluationHom_apply]
    exact (nativeEvaluationHom G T r W b).map_one
  · intro W b x y
    rw [← nativeEvaluationHom_apply, ← nativeEvaluationHom_apply, ← nativeEvaluationHom_apply]
    exact (nativeEvaluationHom G T r W b).map_mul x y

theorem native_group_equations_iff
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G) :
    Group.HomEquations.GroupHomEquations.RespectsGroup G (IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r) ↔ IsMonHom r :=
  ⟨IntrinsicGroupHomPoints.GroupHomEquations.native_isMonHom_of_group_equations G T r,
    fun h => @native_group_equations_of_isMonHom S G _ T r h⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomEquations.GroupHomEquations
