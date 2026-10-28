import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualIdealCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalDerivations

/-! # Dual Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualLifts

noncomputable section

/-! Actual relative dual-number algebra lifts are the coefficient
linear dual of the smooth section's conormal, with an explicit epsilon formula. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RelativeDualLifts
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualIdealCoefficients.AlgebraicLie

variable (R B k : Type) [CommRing R] [CommRing B] [Field k]
  [Algebra R B] [Algebra R k] [Algebra B k] [IsScalarTower R B k]

def Space := LiftDerivations.RelativeLifts.module R B (DualNumber k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)

instance : AddCommGroup (Space R B k) :=
  inferInstanceAs (AddCommGroup (LiftDerivations.RelativeLifts.module R B (DualNumber k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)))

instance : Module (DualNumber k) (Space R B k) :=
  inferInstanceAs (Module (DualNumber k)
    (LiftDerivations.RelativeLifts.module R B (DualNumber k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)))

instance : Module k (Space R B k) := Module.compHom (Space R B k) (algebraMap k (DualNumber k))

instance : IsScalarTower k (DualNumber k) (Space R B k) :=
  by
  constructor
  intro a b v
  change (a • b) • v = (algebraMap k (DualNumber k) a) • (b • v)
  have h : (a • b : DualNumber k) = algebraMap k (DualNumber k) a * b := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, mul_smul]

def derivationEquiv : Space R B k ≃ₗ[k] Derivation R B k := by
  let e : Space R B k ≃ₗ[DualNumber k] Derivation R B (DualNumberReduction.AlgebraicLie.dualIdeal k) :=
    LiftDerivations.RelativeLifts.derivationEquiv R B (DualNumber k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
  exact (e.restrictScalars k).trans (DualIdealCoefficients.AlgebraicLie.derivationDualIdealEquiv k R B)

theorem derivationEquiv_apply (v : Space R B k) (b : B) :
    derivationEquiv R B k v b = (v.val.hom b).snd := by
  change (v.val.hom b - algebraMap B (DualNumber k) b).snd = (v.val.hom b).snd
  rw [TrivSqZeroExt.snd_sub, IsScalarTower.algebraMap_apply B k (DualNumber k),
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, sub_zero]

variable [Algebra B R] [IsScalarTower R B R] [IsScalarTower B R k]
  [Algebra.FormallySmooth R B]

def conormalEquiv : Space R B k ≃ₗ[k]
    ((RingHom.ker (algebraMap B R)).Cotangent →ₗ[R] k) :=
  (derivationEquiv R B k).trans (Section.ConormalDerivations.SectionConormal.derivationConormalEquiv R B k)

theorem conormalEquiv_toCotangent (v : Space R B k) (b : RingHom.ker (algebraMap B R)) :
    conormalEquiv R B k v (Ideal.toCotangent _ b) = (v.val.hom b).snd := by
  change Section.ConormalDerivations.SectionConormal.derivationConormalEquiv R B k (derivationEquiv R B k v)
    (Ideal.toCotangent _ b) = _
  rw [Section.ConormalDerivations.SectionConormal.derivationConormalEquiv_toCotangent, derivationEquiv_apply]

end RelativeDualLifts

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualLifts
