import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SquareZero
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Kaehler.Basic

/-! # Lift Derivations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts

noncomputable section

section

/-! Relative square-zero lifts embed linearly in the actual module of
relative derivations into their square-zero ideal. -/

open scoped TensorProduct

variable (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  (J : Ideal C) (hJ : J ^ 2 = ⊥)

def module : Submodule C (AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift J hJ (algebraMap B C)) where
  carrier := {f | ∀ r : R, f.hom (algebraMap R B r) = algebraMap R C r}
  zero_mem' r := (IsScalarTower.algebraMap_apply R B C r).symm
  add_mem' hf hg r := by
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.add_hom, hf, hg, ← IsScalarTower.algebraMap_apply]
    exact add_sub_cancel_right _ _
  smul_mem' c f hf r := by
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.smul_hom, hf, ← IsScalarTower.algebraMap_apply,
      sub_self, mul_zero, add_zero]

def algebraHom (v : module R B C J hJ) : B →ₐ[R] C :=
  { v.val.hom with commutes' := v.property }

theorem algebraHom_reduction (v : module R B C J hJ) :
    (Ideal.Quotient.mkₐ R J).comp (algebraHom R B C J hJ v) =
      IsScalarTower.toAlgHom R B (C ⧸ J) := by
  apply AlgHom.ext
  intro b
  exact Ideal.Quotient.eq.mpr (v.val.congruent b)

def derivation : module R B C J hJ →ₗ[C] Derivation R B J where
  toFun v := derivationToSquareZeroOfLift J hJ (algebraHom R B C J hJ v)
    (algebraHom_reduction R B C J hJ v)
  map_add' v w := by
    apply Derivation.ext
    intro b
    apply Subtype.ext
    change (v.val + w.val).hom b - algebraMap B C b =
      (v.val.hom b - algebraMap B C b) + (w.val.hom b - algebraMap B C b)
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.add_hom]
    ring
  map_smul' c v := by
    apply Derivation.ext
    intro b
    apply Subtype.ext
    change (c • v.val).hom b - algebraMap B C b = c * (v.val.hom b - algebraMap B C b)
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.smul_hom, add_sub_cancel_left]

theorem derivation_injective : Function.Injective (derivation R B C J hJ) := by
  intro v w h
  apply Subtype.ext
  apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
  apply RingHom.ext
  intro b
  have hb := congrArg (fun d : Derivation R B J => (d b : C)) h
  exact sub_left_injective hb

end

/-! Every relative derivation integrates uniquely to its actual
square-zero algebra lift. This completes the linear cotangent comparison. -/

variable (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  (J : Ideal C) (hJ : J ^ 2 = ⊥)

theorem derivation_surjective : Function.Surjective (derivation R B C J hJ) := by
  intro d
  let f := liftOfDerivationToSquareZero J hJ d
  have hf (b : B) : f b - algebraMap B C b ∈ J := by
    change liftOfDerivationToSquareZero J hJ d b - algebraMap B C b ∈ J
    rw [liftOfDerivationToSquareZero_apply, add_sub_cancel_right]
    exact (d b).property
  let v : module R B C J hJ := ⟨⟨f.toRingHom, hf⟩, fun r => f.commutes r⟩
  refine ⟨v, ?_⟩
  apply Derivation.ext
  intro b
  apply Subtype.ext
  change f b - algebraMap B C b = (d b : C)
  rw [liftOfDerivationToSquareZero_apply, add_sub_cancel_right]

def derivationEquiv : module R B C J hJ ≃ₗ[C] Derivation R B J :=
  LinearEquiv.ofBijective (derivation R B C J hJ)
    ⟨derivation_injective R B C J hJ, derivation_surjective R B C J hJ⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations.RelativeLifts
