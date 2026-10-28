import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tate Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction

noncomputable section

/-! The integral PEL action acts on the actual Tate module and extends
to the integral completion through the tensor product universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime]

def tateEndMap : TateComparison.End.IntegralEnd A →+* Module.End ℤ_[q] (Add.schemeTateModule A T q) where
  toFun f := Add.Tate.map q (f.app (.op T)).hom
  map_zero' := by ext x n; rfl
  map_one' := by ext x n; rfl
  map_add' f g := by ext x n; rfl
  map_mul' f g := by ext x n; rfl

theorem tateEndMap_eq_schemeTateMap (f : TateComparison.End.IntegralEnd A) :
    tateEndMap A T q f = Add.schemeTateMap A T q (TateComparison.End.endSchemeMap A f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrArg Additive.ofMul (TateComparison.End.endSchemeMap_points A f T (x.val n).val.toMul)

variable {R : Type u} [CommRing R] {g N : ℕ}

def tateIntegralAction (F : PEL.PELFamilyData R g N S) :
    R →+* Module.End ℤ_[q] (Add.schemeTateModule F.abelian.scheme T q) :=
  (tateEndMap F.abelian.scheme T q).comp F.action

def tateCompletedAction (F : PEL.PELFamilyData R g N S) :
    ℤ_[q] ⊗[ℤ] R →ₐ[ℤ_[q]] Module.End ℤ_[q] (Add.schemeTateModule F.abelian.scheme T q) :=
  AlgHom.liftEquiv ℤ ℤ_[q] R _ {
    toRingHom := tateIntegralAction T q F
    commutes' z := by
      change (tateIntegralAction T q F) (z : R) =
        z • (1 : Module.End ℤ_[q] (Add.schemeTateModule F.abelian.scheme T q))
      rw [map_intCast]
      ext x
      simp }

theorem tateCompletedAction_tmul (F : PEL.PELFamilyData R g N S) (z : ℤ_[q]) (r : R) :
    tateCompletedAction T q F (z ⊗ₜ[ℤ] r) = z • tateIntegralAction T q F r := by
  rfl

theorem tateCompletedAction_one_tmul (F : PEL.PELFamilyData R g N S) (r : R) :
    tateCompletedAction T q F (1 ⊗ₜ[ℤ] r) =
      Add.schemeTateMap F.abelian.scheme T q (TateComparison.End.endSchemeMap F.abelian.scheme (F.action r)) := by
  rw [tateCompletedAction_tmul, one_smul]
  exact tateEndMap_eq_schemeTateMap F.abelian.scheme T q (F.action r)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction
