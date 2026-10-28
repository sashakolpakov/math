import OAI.AlgebraicGeometry.Divisors.LineBundles.MultiplicationSequence
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Two Equation Symmetry -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationSymmetry.BundleCycles

noncomputable section

/-!
# LineBundleCycles: symmetry of successive local intersection Euler lengths

The double cokernel is the quotient by the sum of the two equation
images. Combined with the actual snake-boundary kernel isomorphism,
this proves symmetry of the finite local intersection invariant.
-/

variable {R : Type*} [CommRing R] (a b : R)

theorem equationQuotient_range :
    (MultiplicationSequence.BundleCycles.equationEndomorphism a (MultiplicationSequence.BundleCycles.equationCokernel b R)).range =
      (MultiplicationSequence.BundleCycles.equationEndomorphism a R).range.map (MultiplicationSequence.BundleCycles.equationEndomorphism b R).range.mkQ := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := (MultiplicationSequence.BundleCycles.equationEndomorphism b R).range.mkQ_surjective q
    refine ⟨MultiplicationSequence.BundleCycles.equationEndomorphism a R x, ⟨x, rfl⟩, ?_⟩
    exact ((MultiplicationSequence.BundleCycles.equationEndomorphism b R).range.mkQ.map_smul a x).trans (congrArg (fun z => a • z) hx)
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(MultiplicationSequence.BundleCycles.equationEndomorphism b R).range.mkQ x, ((MultiplicationSequence.BundleCycles.equationEndomorphism b R).range.mkQ.map_smul a x).symm⟩

/-- The double cokernel is the actual quotient by the sum of the two equation images. -/
def twoEquationCokernelQuotientEquiv :
    MultiplicationSequence.BundleCycles.equationCokernel a (MultiplicationSequence.BundleCycles.equationCokernel b R) ≃ₗ[R]
      R ⧸ ((MultiplicationSequence.BundleCycles.equationEndomorphism b R).range ⊔ (MultiplicationSequence.BundleCycles.equationEndomorphism a R).range) :=
  (Submodule.quotEquivOfEq _ _ (equationQuotient_range a b)).trans
    (Submodule.quotientQuotientEquivQuotientSup (MultiplicationSequence.BundleCycles.equationEndomorphism b R).range (MultiplicationSequence.BundleCycles.equationEndomorphism a R).range)

def twoEquationCokernelEquiv :
    MultiplicationSequence.BundleCycles.equationCokernel a (MultiplicationSequence.BundleCycles.equationCokernel b R) ≃ₗ[R] MultiplicationSequence.BundleCycles.equationCokernel b (MultiplicationSequence.BundleCycles.equationCokernel a R) :=
  (twoEquationCokernelQuotientEquiv a b).trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans (twoEquationCokernelQuotientEquiv b a).symm)

/-- Successive intersection Euler lengths agree under interchange of the two regular equations. -/
theorem equationEulerLength_comm
    (ha : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism a R))
    (hb : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism b R))
    (hKab : Module.length R (MultiplicationSequence.BundleCycles.equationKernel a (MultiplicationSequence.BundleCycles.equationCokernel b R)) ≠ ⊤)
    (hCab : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel a (MultiplicationSequence.BundleCycles.equationCokernel b R)) ≠ ⊤)
    (hKba : Module.length R (MultiplicationSequence.BundleCycles.equationKernel b (MultiplicationSequence.BundleCycles.equationCokernel a R)) ≠ ⊤)
    (hCba : Module.length R (MultiplicationSequence.BundleCycles.equationCokernel b (MultiplicationSequence.BundleCycles.equationCokernel a R)) ≠ ⊤) :
    EquationEulerLength.BundleCycles.equationEulerLength a (MultiplicationSequence.BundleCycles.equationCokernel b R) hKab hCab =
      EquationEulerLength.BundleCycles.equationEulerLength b (MultiplicationSequence.BundleCycles.equationCokernel a R) hKba hCba := by
  unfold EquationEulerLength.BundleCycles.equationEulerLength
  rw [(MultiplicationSequence.BundleCycles.twoEquationKernelEquiv a b hb ha).length_eq, (twoEquationCokernelEquiv a b).length_eq]

theorem equationEndomorphism_injective [IsDomain R] (ha : a ≠ 0) : Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism a R) := by
  intro x y h
  change a * x = a * y at h
  exact mul_left_cancel₀ ha h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.TwoEquationSymmetry.BundleCycles
