import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousInnerDerivations
import Mathlib.Topology.Instances.Matrix

/-! # Killing Determinant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.KillingDeterminant.Construction

noncomputable section

/-! The determinant of the Killing form is continuous in the bracket.
Changing basis multiplies it by the inverse square determinant. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance killingDetEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance killingDetEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance killingDetEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance killingDetBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance killingDetBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

def continuousEndTrace : (L →L[ℝ] L) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ L).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

theorem continuousBracketKillingForm_continuous (x y : L) :
    Continuous (fun B : L →L[ℝ] L →L[ℝ] L => ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x y) := by
  have hx : Continuous (fun B : L →L[ℝ] L →L[ℝ] L => B x) :=
    continuous_id.clm_apply continuous_const
  have hy : Continuous (fun B : L →L[ℝ] L →L[ℝ] L => B y) :=
    continuous_id.clm_apply continuous_const
  exact continuousEndTrace.continuous.comp (hx.clm_comp hy)

theorem continuousBracketKillingForm_change (e : L ≃L[ℝ] L)
    (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    ContinuousInnerDerivations.Construction.continuousBracketKillingForm (ContinuousBracketChange.Construction.continuousBracketChange e B) x y =
      ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (e.symm x) (e.symm y) := by
  have he (z : L) : (ContinuousBracketChange.Construction.continuousBracketChange e B z).toLinearMap =
      e.toLinearEquiv.conjAlgEquiv ℝ ((B (e.symm z)).toLinearMap) := by
    ext w
    rfl
  rw [ContinuousInnerDerivations.Construction.continuousBracketKillingForm_apply, he, he, ← map_mul, LinearMap.trace_map]
  rfl

def bracketKillingDeterminant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L) : ℝ :=
  (LinearMap.BilinForm.toMatrix b (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B)).det

theorem bracketKillingDeterminant_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L) :
    bracketKillingDeterminant b B ≠ 0 ↔ (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).symm

theorem bracketKillingDeterminant_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ L) : Continuous (bracketKillingDeterminant b) := by
  have hm : Continuous (fun B : L →L[ℝ] L →L[ℝ] L =>
      LinearMap.BilinForm.toMatrix b (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa only [LinearMap.BilinForm.toMatrix_apply] using
      continuousBracketKillingForm_continuous (b i) (b j)
  exact hm.matrix_det

theorem bracketKillingDeterminant_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ L) (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    LinearMap.det e.toLinearMap ^ 2 * bracketKillingDeterminant b (ContinuousBracketChange.Construction.continuousBracketChange e B) =
      bracketKillingDeterminant b B := by
  have he : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (ContinuousBracketChange.Construction.continuousBracketChange e B)).comp
      e.toLinearMap e.toLinearMap = ContinuousInnerDerivations.Construction.continuousBracketKillingForm B := by
    ext x y
    exact (continuousBracketKillingForm_change e B (e x) (e y)).trans (by simp)
  have hm := congrArg (fun Q : LinearMap.BilinForm ℝ L => (LinearMap.BilinForm.toMatrix b Q).det) he
  rw [LinearMap.BilinForm.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, LinearMap.det_toMatrix] at hm
  change _ * bracketKillingDeterminant b (ContinuousBracketChange.Construction.continuousBracketChange e B) * _ = _ at hm
  convert hm using 1
  · ring
  · rfl

theorem bracketKillingDeterminant_change_of_abs_det_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ L)
    (e : L ≃L[ℝ] L) (he : |LinearMap.det e.toLinearMap| = 1)
    (B : L →L[ℝ] L →L[ℝ] L) :
    bracketKillingDeterminant b (ContinuousBracketChange.Construction.continuousBracketChange e B) = bracketKillingDeterminant b B := by
  have hs : LinearMap.det e.toLinearMap ^ 2 = 1 := by
    rw [← sq_abs, he, one_pow]
  simpa only [hs, one_mul] using bracketKillingDeterminant_change b e B

theorem abs_det_one_of_bracketKillingDeterminant_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ L)
    (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (he : bracketKillingDeterminant b (ContinuousBracketChange.Construction.continuousBracketChange e B) = bracketKillingDeterminant b B) :
    |LinearMap.det e.toLinearMap| = 1 := by
  have hs := bracketKillingDeterminant_change b e B
  rw [he] at hs
  have hne := (bracketKillingDeterminant_ne_zero b B).mpr hB
  have hsq : LinearMap.det e.toLinearMap ^ 2 = 1 :=
    (mul_right_cancel₀ hne) (hs.trans (one_mul _).symm)
  nlinarith [sq_abs (LinearMap.det e.toLinearMap), abs_nonneg (LinearMap.det e.toLinearMap)]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.KillingDeterminant.Construction
