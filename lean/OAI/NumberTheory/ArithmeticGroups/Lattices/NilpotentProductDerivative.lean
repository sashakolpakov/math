import OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleStrictDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential
import Mathlib.LinearAlgebra.Projection

/-! # Nilpotent Product Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductDerivative.Construction

noncomputable section

/-! Products of two exponential factors give local coordinates when
their tangent subspaces are complementary. -/

open NormedSpace _root_.ContinuousLinearMap

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem exponential_product_sub_one_mem
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (x y : W) : exp x.val * exp y.val - 1 ∈ W := by
  have he : exp x.val * exp y.val - 1 =
      (exp x.val - 1) * (exp y.val - 1) + (exp x.val - 1) + (exp y.val - 1) := by
    noncomm_ring
  rw [he]
  exact W.add_mem (W.add_mem (hmul _ (hexp x.val x.property) _ (hexp y.val y.property))
    (hexp x.val x.property)) (hexp y.val y.property)

def exponentialProductCoordinates
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W) : U × V → W :=
  fun p => ⟨exp p.1.val.val * exp p.2.val.val - 1,
    exponential_product_sub_one_mem W hmul hexp p.1.val p.2.val⟩

omit [CompleteSpace A] in
theorem exponentialProductCoordinates_zero
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W) :
    exponentialProductCoordinates W hmul hexp U V 0 = 0 := by
  apply Subtype.ext
  change exp (0 : A) * exp 0 - 1 = 0
  rw [exp_zero, mul_one, sub_self]

theorem exponentialProductCoordinates_continuous
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W) :
    Continuous (exponentialProductCoordinates W hmul hexp U V) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hx : Continuous (fun p : U × V => p.1.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hy : Continuous (fun p : U × V => p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact (((exp_continuous.comp hx).mul (exp_continuous.comp hy)).sub continuous_const).subtype_mk _

theorem exponentialProductCoordinates_hasStrictFDerivAt
    [FiniteDimensional ℝ A]
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W) (hUV : IsCompl U V) :
    HasStrictFDerivAt (exponentialProductCoordinates W hmul hexp U V)
      (U.prodEquivOfIsCompl V hUV).toContinuousLinearEquiv.toContinuousLinearMap 0 := by
  let a : U × V →L[ℝ] A := W.subtypeL.comp (U.subtypeL.comp (ContinuousLinearMap.fst ℝ U V))
  let b : U × V →L[ℝ] A := W.subtypeL.comp (V.subtypeL.comp (ContinuousLinearMap.snd ℝ U V))
  have hd : HasStrictFDerivAt (fun p => exp (a p) * exp (b p) - 1) (a + b) 0 := by
    have ha : HasStrictFDerivAt (fun p => exp (a p)) a 0 :=
      Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero (E := U × V) (A := A) a
    have hb : HasStrictFDerivAt (fun p => exp (b p)) b 0 :=
      Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero (E := U × V) (A := A) b
    have hm := HasStrictFDerivAt.mul' (𝕜 := ℝ) (x := (0 : U × V)) ha hb
    convert! hm.sub_const (1 : A) using 1
    apply ContinuousLinearMap.ext
    intro p
    change a p + b p = exp (a 0) * b p + a p * exp (b 0)
    simp only [map_zero, exp_zero, one_mul, mul_one]
    exact add_comm _ _
  apply SubmoduleStrictDerivative.Construction.hasStrictFDerivAt_submodule W (exponentialProductCoordinates W hmul hexp U V)
    (U.prodEquivOfIsCompl V hUV).toContinuousLinearEquiv.toContinuousLinearMap 0
  exact hd

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductDerivative.Construction
