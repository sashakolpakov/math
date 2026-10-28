import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation

/-! # Torsion Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionAction

noncomputable section

/-! The actual PEL action on torsion levels and its completion. Tate
evaluation intertwines these actions, including the completed coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime] (n : ℕ)

def torsionEndMap : TateComparison.End.IntegralEnd A →+* Module.End ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ A)) n) where
  toFun f := Add.Tate.mapLevel q (f.app (.op T)).hom n
  map_zero' := by ext x; rfl
  map_one' := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_mul' f g := by ext x; rfl

variable {R : Type u} [CommRing R] {g N : ℕ}

def torsionIntegralAction (F : PEL.PELFamilyData R g N S) :
    R →+* Module.End ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  (torsionEndMap F.abelian.scheme T q n).comp F.action

def torsionCompletedAction (F : PEL.PELFamilyData R g N S) :
    ℤ_[q] ⊗[ℤ] R →ₐ[ℤ_[q]] Module.End ℤ_[q]
      (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  AlgHom.liftEquiv ℤ ℤ_[q] R _ {
    toRingHom := torsionIntegralAction T q n F
    commutes' z := by
      change (torsionIntegralAction T q n F) (z : R) =
        z • (1 : Module.End ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n))
      rw [map_intCast]
      ext x
      simp }

theorem torsionCompletedAction_tmul (F : PEL.PELFamilyData R g N S) (z : ℤ_[q]) (r : R) :
    torsionCompletedAction T q n F (z ⊗ₜ[ℤ] r) = z • torsionIntegralAction T q n F r := rfl

theorem evaluate_integralAction (F : PEL.PELFamilyData R g N S) (r : R) :
    (Evaluation.Tate.evaluate q n).comp (TateAction.tateIntegralAction T q F r) =
      (torsionIntegralAction T q n F r).comp (Evaluation.Tate.evaluate q n) := rfl

theorem evaluate_completedAction (F : PEL.PELFamilyData R g N S) (z : ℤ_[q] ⊗[ℤ] R) :
    (Evaluation.Tate.evaluate q n).comp (TateAction.tateCompletedAction T q F z) =
      (torsionCompletedAction T q n F z).comp (Evaluation.Tate.evaluate q n) := by
  induction z using TensorProduct.inductionOn with
  | tmul a r =>
    rw [TateAction.tateCompletedAction_tmul, torsionCompletedAction_tmul, LinearMap.comp_smul,
      LinearMap.smul_comp, evaluate_integralAction T q n F r]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionAction
