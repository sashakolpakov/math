import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange

/-! # Intrinsic Group Hom Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomPoints.GroupHomEquations

noncomputable section

/-! A family satisfying the constructed group equations is an actual
group-scheme endomorphism of the native pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (G : Over S) [GrpObj G] (T : Over S)

def parameterProjection (Q : Over T.left) : (Over.map T.hom).obj Q ⟶ T :=
  Over.homMk Q.hom rfl

theorem point_pair_source (Q : Over T.left)
    (x : Q ⟶ (Over.pullback T.hom).obj G) :
    (prod.lift (parameterProjection T Q) (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q x)).left ≫
      (IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso G T).hom = x.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_fst,
      ← Over.comp_left, prod.lift_snd]
    rfl
  · rw [Category.assoc, IntrinsicPointedDescent.PointedLiftParameters.nativeSourceSchemeIso_snd,
      ← Over.comp_left, prod.lift_fst]
    exact x.w.symm

theorem native_evaluation (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G)
    (Q : Over T.left) (x : Q ⟶ (Over.pullback T.hom).obj G) :
    Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q (x ≫ r) =
      prod.lift (parameterProjection T Q) (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q x) ≫
        IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv_left,
    ← Category.assoc, ← Category.assoc, point_pair_source]
  rfl

theorem native_isMonHom_of_group_equations
    (r : (Over.pullback T.hom).obj G ⟶ (Over.pullback T.hom).obj G)
    (hr : Group.HomEquations.GroupHomEquations.RespectsGroup G (IntrinsicPointedDescent.PointedLiftParameters.nativeHomEquiv G G T r)) : IsMonHom r := by
  let A := (Over.pullback T.hom).obj G
  have ho (Q : Over T.left) : (1 : Q ⟶ A) ≫ r = 1 := by
    let e := Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q
    apply e.injective
    change Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q ((1 : Q ⟶ A) ≫ r) = e 1
    rw [native_evaluation]
    rw [e.map_one]
    exact Group.HomEvaluation.GroupHomEquations.eval_one G _ hr (parameterProjection T Q)
  have hm (Q : Over T.left) (x y : Q ⟶ A) : (x * y) ≫ r = (x ≫ r) * (y ≫ r) := by
    let e := Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q
    apply e.injective
    rw [e.map_mul]
    change Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q ((x * y) ≫ r) =
      Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q (x ≫ r) *
        Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv G T.hom Q (y ≫ r)
    rw [native_evaluation, native_evaluation, native_evaluation]
    rw [e.map_mul]
    exact Group.HomEvaluation.GroupHomEquations.eval_mul G _ hr (parameterProjection T Q) (e x) (e y)
  refine ⟨?_, ?_⟩
  · simpa only [MonObj.one_eq_one] using ho (𝟙_ (Over T.left))
  · simpa only [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp] using
      hm (A ⊗ A) (fst A A) (snd A A)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicGroupHomPoints.GroupHomEquations
