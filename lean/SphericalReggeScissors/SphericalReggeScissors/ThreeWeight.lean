/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors.ExternalInputs

/-!
# The internal three-weight argument

This file formalizes the short logical core hidden by the motivic
terminology.  Once the primitive kernel of the middle coproduct is
identified with `H¹(U,ℚ(2))`, and that group is zero, any class with zero
middle coproduct is zero.  No construction of motives is needed for this
deduction; that construction is isolated in `MotivicInputs`.
-/

namespace SphericalReggeScissors

universe uU uM uL uA uH

section ThreeWeight

variable {Universal : Type uU} {Middle : Type uM} {H1 : Type uH}
variable [AddCommGroup Universal] [Module ℚ Universal]
variable [AddCommGroup Middle] [Module ℚ Middle]
variable [AddCommGroup H1] [Module ℚ H1]

/-- The explicit split-cover computation descends to equality of the two
relative middle coproducts.  Notice that finite-étale descent is used only
through the named injectivity field. -/
theorem coproduct_eq_of_six_channel_calculation
    {LeftFactor : Type uL} {RightFactor : Type uA}
    [AddCommGroup LeftFactor] [Module ℚ LeftFactor]
    [AddCommGroup RightFactor] [Module ℚ RightFactor]
    (I : MotivicInputs Universal Middle H1)
    (B : CoproductBridge Universal Middle LeftFactor RightFactor I.coproduct) :
    I.coproduct B.relativeOriginal = I.coproduct B.relativeReggeMate := by
  apply B.finite_etale_sign_trace_injective
  rw [B.split_formula_original, B.split_formula_reggeMate]
  exact (six_channel_tensor_invariance B.movingLeft B.movingRight
    B.fixedLeft₀ B.fixedLeft₁ B.fixedRight₀ B.fixedRight₁).symm

/-- The universal Regge difference has zero middle coproduct.  This is
derived from the coordinate invariant and the two coproduct-formula
bridges; it is deliberately not an input field. -/
theorem coproduct_of_regge_difference_eq_zero
    {LeftFactor : Type uL} {RightFactor : Type uA}
    [AddCommGroup LeftFactor] [Module ℚ LeftFactor]
    [AddCommGroup RightFactor] [Module ℚ RightFactor]
    (I : MotivicInputs Universal Middle H1)
    (B : CoproductBridge Universal Middle LeftFactor RightFactor I.coproduct) :
    I.coproduct (B.relativeOriginal - B.relativeReggeMate) = 0 := by
  rw [map_sub, sub_eq_zero]
  exact coproduct_eq_of_six_channel_calculation I B

/-- The primitive-kernel-to-`H¹` comparison plus `H¹ = 0` makes the
primitive kernel trivial. -/
theorem primitive_eq_zero
    (I : MotivicInputs Universal Middle H1)
    {x : Universal} (hx : I.coproduct x = 0) : x = 0 := by
  let xKer : I.coproduct.ker := ⟨x, hx⟩
  have hImage : I.primitiveComparison xKer = 0 :=
    I.h1_vanishes (I.primitiveComparison xKer)
  have hKer : xKer = 0 := by
    apply I.primitiveComparison.injective
    simpa using hImage
  exact congrArg Subtype.val hKer

/-- Difference form of the same argument: equality of middle coproducts
forces equality of framed coefficients. -/
theorem eq_of_coproduct_eq
    (I : MotivicInputs Universal Middle H1)
    {x y : Universal} (hxy : I.coproduct x = I.coproduct y) : x = y := by
  apply sub_eq_zero.mp
  apply primitive_eq_zero I
  simpa [map_sub] using sub_eq_zero.mpr hxy

/-- The manuscript's universal framed-defect theorem, with the deep
motivic statements visible as fields of `I`. -/
theorem universal_framed_defect_vanishes
    (I : MotivicInputs Universal Middle H1)
    (defect : Universal) (hcoproduct : I.coproduct defect = 0) : defect = 0 :=
  primitive_eq_zero I hcoproduct

end ThreeWeight

end SphericalReggeScissors
