import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerLength
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Equation Euler Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv.BundleCycles

noncomputable section

/-!
# LineBundleCycles: multiplication Euler lengths under actual module isomorphisms

Linearity gives compatibility with multiplication by the equation.
The induced kernel and cokernel isomorphisms preserve their finite
lengths, allowing prime-filtration factors to use their actual R/p
presentations.
-/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a : R) (e : M ≃ₗ[R] N)

theorem equationKernel_map_equiv : (MultiplicationSequence.BundleCycles.equationKernel a M).map e.toLinearMap = MultiplicationSequence.BundleCycles.equationKernel a N := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change a • e x = 0
    change a • x = 0 at hx
    exact (e.map_smul a x).symm.trans ((congrArg e hx).trans e.map_zero)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change a • e.symm y = 0
    change a • y = 0 at hy
    exact (e.symm.map_smul a y).symm.trans ((congrArg e.symm hy).trans e.symm.map_zero)

def equationKernelEquiv : MultiplicationSequence.BundleCycles.equationKernel a M ≃ₗ[R] MultiplicationSequence.BundleCycles.equationKernel a N :=
  e.ofSubmodules _ _ (equationKernel_map_equiv a e)

theorem equationRange_map_equiv :
    (MultiplicationSequence.BundleCycles.equationEndomorphism a M).range.map e.toLinearMap = (MultiplicationSequence.BundleCycles.equationEndomorphism a N).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (e.map_smul a x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨a • e.symm x, ⟨e.symm x, rfl⟩, ?_⟩
    exact (e.map_smul a (e.symm x)).trans (congrArg (fun y => a • y) (e.apply_symm_apply x))

def equationCokernelEquiv : MultiplicationSequence.BundleCycles.equationCokernel a M ≃ₗ[R] MultiplicationSequence.BundleCycles.equationCokernel a N :=
  Submodule.Quotient.equiv _ _ e (equationRange_map_equiv a e)

include e

theorem equationKernel_length_equiv : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) = Module.length R (MultiplicationSequence.BundleCycles.equationKernel a N) :=
  (equationKernelEquiv a e).length_eq

theorem equationCokernel_length_equiv : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) = Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a N) :=
  (equationCokernelEquiv a e).length_eq

theorem equationEulerLength_equiv
    (hKM : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a M) ≠ ⊤)
    (hCM : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a M) ≠ ⊤)
    (hKN : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a N) ≠ ⊤)
    (hCN : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a N) ≠ ⊤) :
    EquationEulerLength.BundleCycles.equationEulerLength a M hKM hCM = EquationEulerLength.BundleCycles.equationEulerLength a N hKN hCN := by
  unfold EquationEulerLength.BundleCycles.equationEulerLength
  rw [equationKernel_length_equiv a e, equationCokernel_length_equiv a e]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv.BundleCycles
