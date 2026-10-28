import Mathlib.Algebra.Algebra.Rat
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Rational Retraction -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RationalRetraction

/-!
# A rational-linear retraction of the rational inclusion into the complex numbers

The inclusion `ℚ → ℂ` is injective. Mathlib's basis-extension construction
`LinearMap.leftInverse` therefore supplies an actual `ℚ`-linear left inverse.
This retraction is chosen noncomputably; continuity is neither claimed nor needed
for postcomposition of singular cochains with discrete coefficient modules.

There are no additional assumptions on the coefficient maps in this file.
-/

/-- The usual inclusion of rational numbers into complex numbers, as a
rational-linear map. -/
noncomputable def rationalInclusion : ℚ →ₗ[ℚ] ℂ :=
  Algebra.linearMap ℚ ℂ

@[simp]
theorem rationalInclusion_apply (q : ℚ) : rationalInclusion q = (q : ℂ) := by
  simp [rationalInclusion]

/-- Rational numbers retain their distinct values under the usual complex inclusion. -/
theorem rationalInclusion_injective : Function.Injective rationalInclusion := by
  intro p q h
  exact Rat.cast_injective (α := ℂ) (by simpa only [rationalInclusion_apply] using h)

/-- The usual rational inclusion has zero kernel. -/
theorem rationalInclusion_ker : LinearMap.ker rationalInclusion = ⊥ :=
  LinearMap.ker_eq_bot.mpr rationalInclusion_injective

/-- A rational-linear retraction of the usual inclusion into the complex numbers,
constructed using mathlib's extension of a linearly independent set to a basis. -/
noncomputable def rationalRetraction : ℂ →ₗ[ℚ] ℚ :=
  rationalInclusion.leftInverse

/-- The selected retraction composed with the usual inclusion is the identity. -/
@[simp]
theorem rationalRetraction_comp_inclusion :
    rationalRetraction.comp rationalInclusion = LinearMap.id :=
  LinearMap.leftInverse_comp_of_inj rationalInclusion_ker

/-- The retraction recovers every rational number from its complex image. -/
@[simp]
theorem rationalRetraction_ratCast (q : ℚ) : rationalRetraction (q : ℂ) = q := by
  simpa [rationalRetraction] using
    (LinearMap.leftInverse_apply_of_inj rationalInclusion_ker q)

/-- The coefficient maps split as ordinary functions as well as linear maps. -/
theorem rationalRetraction_leftInverse :
    Function.LeftInverse rationalRetraction rationalInclusion := by
  intro q
  exact (rationalInclusion_apply q) ▸ rationalRetraction_ratCast q

/-- The retraction is onto the rational numbers. -/
theorem rationalRetraction_surjective : Function.Surjective rationalRetraction :=
  rationalRetraction_leftInverse.surjective

end OAI.AlgebraicTopology.Cohomology.Singular.RationalRetraction
