import OAI.Analysis.Normed.Function.Holder.Moore

open scoped Matrix.Norms.Elementwise ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.LinearAlgebra.Moore

variable {X : Type*} [MetricSpace X] {α : ℝ}

def fieldEvaluation {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : X) :
    HolderMap X F α →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM

@[simp] theorem fieldEvaluation_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : X) (f : HolderMap X F α) : fieldEvaluation x f = OAI.Analysis.Normed.Function.Holder.HolderMap.value f x := rfl

/-- The derivative in the Hölder Banach norm is exactly the pointwise
Moore-determinant differential already established algebraically. -/
theorem fderiv_mooreDetField_value (hα : 0 ≤ α) (n : ℕ)
    (A D : HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDetField hα n) A D) x =
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x) := by
  have hp : HasDerivAt (fun t : ℝ ↦ A + t • D) D 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add A
  have hF := ((contDiff_mooreDetField (X := X) hα n 1).differentiable
    (by norm_num) (A + (0 : ℝ) • D)).hasFDerivAt
  have hc := hF.comp_hasDerivAt 0 hp
  have he := (fieldEvaluation (α := α) (F := ℝ) x).hasFDerivAt.comp_hasDerivAt 0 hc
  have he' : HasDerivAt (fun t : ℝ ↦ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A + t • D) x))
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDetField hα n) A D) x) 0 := by
    simpa only [Function.comp_def, fieldEvaluation_apply, value_mooreDetField,
      zero_smul, add_zero] using he
  have hentry (i j : Fin n) :
      HasDerivAt (fun t : ℝ ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value (A + t • D) x i j)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x i j) 0 := by
    change HasDerivAt (fun t : ℝ ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j + t • OAI.Analysis.Normed.Function.Holder.HolderMap.value D x i j)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x i j) 0
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x i j)).const_add
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j)
  have hr := OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_path n (fun t : ℝ ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.value (A + t • D) x)
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x) 0 hentry
  exact he'.unique (by simpa only [zero_smul, add_zero] using hr)

end OAI.Analysis.Normed.Function.Holder
