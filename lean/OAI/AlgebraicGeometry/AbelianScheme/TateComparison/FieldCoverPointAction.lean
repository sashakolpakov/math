import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralFieldDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

/-! # Field Cover Point Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldCoverPointAction

noncomputable section

/-! Values of a map on the field-extension cover are the transported
endomorphism values at the corresponding original-base points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k L : Type u} [Field k] [Field L]
  (p : Spec (.of L) ⟶ Spec (.of k)) (A : Over (Spec (.of k)))
  {T : Scheme.{u}} {b : T ⟶ Spec (.of k)} (x : Over.mk b ⟶ FieldGeometricDescent.fieldSource p A)

def fieldCoverPointToBase : T ⟶ Spec (.of L) := x.left ≫ pullback.snd A.hom p

theorem fieldCoverPointToBase_comp : fieldCoverPointToBase p A x ≫ p = b := by
  change (x.left ≫ pullback.snd A.hom p) ≫ p = b
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact x.w

def fieldCoverPointLift : Over.mk (fieldCoverPointToBase p A x) ⟶ (Over.pullback p).obj A :=
  Over.homMk x.left rfl

theorem fieldCoverPoint_transport [GrpObj A] :
    FieldPointTransport.pointBaseChangeMulEquiv p (fieldCoverPointToBase p A x) b
      (fieldCoverPointToBase_comp p A x) A (fieldCoverPointLift p A x) =
        x ≫ FieldGeometricDescent.fieldSourceProjection p A := by
  apply Over.OverMorphism.ext
  rw [FieldPointTransport.pointBaseChangeMulEquiv_left]
  rfl

theorem fieldEndUnderlying_point_action [GrpObj A]
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) [IsMonHom φ] :
    FieldPointTransport.pointBaseChangeEnd p (fieldCoverPointToBase p A x) b
      (fieldCoverPointToBase_comp p A x) A φ
      (Additive.ofMul (x ≫ FieldGeometricDescent.fieldSourceProjection p A)) =
        Additive.ofMul (x ≫ IntegralFieldDescent.fieldEndUnderlying p A φ) := by
  rw [← fieldCoverPoint_transport p A x, FieldPointTransport.pointBaseChangeEnd_apply]
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  rw [FieldPointTransport.pointBaseChangeMulEquiv_left]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldCoverPointAction
