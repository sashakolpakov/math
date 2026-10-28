import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LiePoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftFiniteness
import Mathlib.RingTheory.Finiteness.Prod

/-! # Lie Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiniteness

noncomputable section

/-! The intrinsic algebraic Lie space of a locally finite-type group
scheme is finite dimensional over its field, in every characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AlgebraicLie

variable {k : Type} [Field k] (A : Over (Spec (.of k))) [MonObj A]

instance spaceScalarTower : IsScalarTower k (DualNumber k) (LiePoints.AlgebraicLie.Space A) := by
  constructor
  intro a b v
  change (a • b) • v = (algebraMap k (DualNumber k) a) • (b • v)
  have h : (a • b : DualNumber k) = algebraMap k (DualNumber k) a * b := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, mul_smul]

instance space_finite [LocallyOfFiniteType A.hom] : Module.Finite k (LiePoints.AlgebraicLie.Space A) := by
  let : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  let : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  let : Module.Finite (DualNumber k) (LiePoints.AlgebraicLie.Space A) :=
    StalkLiftFiniteness.finite_group_tangent (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualBase k)
      (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A
  exact Module.Finite.trans (R := k) (DualNumber k) (LiePoints.AlgebraicLie.Space A)

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiniteness
