import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PointedLifts

/-! # Field Group Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGroupPoints

noncomputable section

/-! Exact group-valued comparison between points of a field base change
and points over the specified field morphism. The source test object is
literally Over.mk of that morphism, as required by arithmetic descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def homDomainMulEquiv {S : Scheme.{u}} {U V : Over S} (e : U ≅ V)
    (H : Over S) [GrpObj H] : (V ⟶ H) ≃* (U ⟶ H) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := e.inv_hom_id_assoc f
  right_inv f := e.hom_inv_id_assoc f
  map_mul' f g := MonObj.comp_mul e.hom f g

def fieldUnitIso {k : Type u} [Field k] {S : Scheme.{u}} (φ : Spec (.of k) ⟶ S) :
    (Over.map φ).obj (Over.mk (𝟙 (Spec (.of k)))) ≅ Over.mk φ :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (.of k)) ≫ φ = 𝟙 (Spec (.of k)) ≫ φ
    rfl)

def fieldGroupPointsMulEquiv {k : Type u} [Field k] {S : Scheme.{u}}
    (φ : Spec (.of k) ⟶ S) (H : Over S) [GrpObj H] :
    CountableParameters.ParameterPoints ((Over.pullback φ).obj H) ≃* (Over.mk φ ⟶ H) :=
  (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv H φ (Over.mk (𝟙 _))).trans
    (homDomainMulEquiv (fieldUnitIso φ).symm H)

theorem fieldGroupPointsMulEquiv_left {k : Type u} [Field k] {S : Scheme.{u}}
    (φ : Spec (.of k) ⟶ S) (H : Over S) [GrpObj H]
    (p : CountableParameters.ParameterPoints ((Over.pullback φ).obj H)) :
    (fieldGroupPointsMulEquiv φ H p).left = p.left ≫ pullback.fst H.hom φ := by
  change 𝟙 (Spec (.of k)) ≫ (p.left ≫ pullback.fst H.hom φ) = _
  exact Category.id_comp _

theorem fieldGroupPointsMulEquiv_symm_fst {k : Type u} [Field k] {S : Scheme.{u}}
    (φ : Spec (.of k) ⟶ S) (H : Over S) [GrpObj H] (p : Over.mk φ ⟶ H) :
    ((fieldGroupPointsMulEquiv φ H).symm p).left ≫ pullback.fst H.hom φ = p.left :=
  (fieldGroupPointsMulEquiv_left φ H _).symm.trans
    (congrArg Over.Hom.left ((fieldGroupPointsMulEquiv φ H).apply_symm_apply p))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGroupPoints
