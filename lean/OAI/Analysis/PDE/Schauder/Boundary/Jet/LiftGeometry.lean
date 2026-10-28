import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Reflection

noncomputable section
open InnerProductSpace
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def normalProjectionMap (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ e).smulRight e

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalProjectionMap_apply (e x : E) :
    normalProjectionMap e x = normalProjection e x := rfl

omit [FiniteDimensional ℝ E] in
theorem normalProjection_eq_half (e : E) (he : ‖e‖ = 1) (x : E) :
    normalProjection e x = (1 / 2 : ℝ) • (x + normalReflection e x) := by
  rw [normalReflection_apply e x he]
  dsimp only [normalProjection]
  module

omit [FiniteDimensional ℝ E] in
theorem norm_normalProjection_le (e : E) (he : ‖e‖ = 1) (x : E) :
    ‖normalProjection e x‖ ≤ ‖x‖ := by
  rw [normalProjection_eq_half e he, norm_smul, Real.norm_eq_abs]
  have hn : ‖normalReflection e x‖ = ‖x‖ := (normalReflection e).norm_map x
  have ht := norm_add_le x (normalReflection e x)
  rw [hn] at ht
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

omit [FiniteDimensional ℝ E] in
theorem norm_normalProjectionMap_le (e : E) (he : ‖e‖ = 1) :
    ‖normalProjectionMap e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul, normalProjectionMap_apply] using norm_normalProjection_le e he x

def normalRegularizationMap (e : E) : E →L[ℝ] ℝ × E :=
  (innerSL ℝ e).prod (normalProjectionMap e)

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalRegularizationMap_apply (e x : E) :
    normalRegularizationMap e x = (inner ℝ e x, normalProjection e x) := rfl

omit [FiniteDimensional ℝ E] in
theorem norm_normalRegularizationMap_le (e : E) (he : ‖e‖ = 1) :
    ‖normalRegularizationMap e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [normalRegularizationMap_apply, Prod.norm_def, max_le_iff, one_mul]
  constructor
  · simpa only [Real.norm_eq_abs, he, one_mul] using abs_real_inner_le_norm e x
  · exact norm_normalProjection_le e he x

end OAI.Analysis.PDE.Schauder
