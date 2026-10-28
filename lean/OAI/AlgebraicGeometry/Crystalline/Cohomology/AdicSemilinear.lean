import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear

/-! # Adic Semilinear -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicSemilinear.AdicSemilinearEquiv

noncomputable section

/-! # Semilinear equivalences pass through compatible adic completions -/

universe u

variable {R S M N : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
  (h : Ideal.map σ.toRingHom I ≤ J) (h' : Ideal.map σ.symm.toRingHom J ≤ I)

local instance forwardScalarInverse : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance backwardScalarInverse : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.symm σ.toRingHom σ.symm.toRingHom

variable (f : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) M N)

def forward : AdicCompletion I M →ₛₗ[σ.toRingHom] AdicCompletion J N :=
  NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.map σ.toRingHom I J h f.toLinearMap

def backward : AdicCompletion J N →ₛₗ[σ.symm.toRingHom] AdicCompletion I M :=
  NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.map σ.symm.toRingHom J I h' f.symm.toLinearMap

theorem left_inverse : Function.LeftInverse (backward σ I J h' f) (forward σ I J h f) := by
  intro x
  apply AdicCompletion.ext
  intro n
  change NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ.symm.toRingHom J I h' f.symm.toLinearMap n
    (NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ.toRingHom I J h f.toLinearMap n (x.val n)) = x.val n
  generalize x.val n = q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    change Submodule.Quotient.mk (f.symm (f y)) = Submodule.Quotient.mk y
    rw [LinearEquiv.symm_apply_apply]

theorem right_inverse : Function.RightInverse (backward σ I J h' f) (forward σ I J h f) := by
  intro x
  apply AdicCompletion.ext
  intro n
  change NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ.toRingHom I J h f.toLinearMap n
    (NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.reduce σ.symm.toRingHom J I h' f.symm.toLinearMap n (x.val n)) = x.val n
  generalize x.val n = q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    change Submodule.Quotient.mk (f (f.symm y)) = Submodule.Quotient.mk y
    rw [LinearEquiv.apply_symm_apply]

def equiv : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) (AdicCompletion I M) (AdicCompletion J N) where
  __ := forward σ I J h f
  invFun := backward σ I J h' f
  left_inv := left_inverse σ I J h h' f
  right_inv := right_inverse σ I J h h' f

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicSemilinear.AdicSemilinearEquiv
