import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.IsTensorProduct

/-! # Pushout Module -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PushoutModule.Construction.PushoutModuleIso

noncomputable section

/-! The module tensor comparison associated to a pushout of commutative rings. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R A B P : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing P]
variable [Algebra R A] [Algebra R B] [Algebra R P] [Algebra A P] [Algebra B P]
variable [IsScalarTower R A P] [IsScalarTower R B P] [Algebra.IsPushout R B A P]
variable (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable [AddCommGroup N] [Module P N] [Module B N] [IsScalarTower B P N]
variable (q : P ⊗[A] M ≃ₗ[P] N)

def iso : ModuleCat.of B (B ⊗[R] M) ≅ ModuleCat.of B N :=
  ((Algebra.IsPushout.cancelBaseChange R B A P M).symm.trans (q.restrictScalars B)).toModuleIso

theorem one_tmul (m : M) : (iso R A B P M N q).hom (1 ⊗ₜ[R] m) = q (1 ⊗ₜ[A] m) := by
  change q ((Algebra.IsPushout.cancelBaseChange R B A P M).symm (1 ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PushoutModule.Construction.PushoutModuleIso
