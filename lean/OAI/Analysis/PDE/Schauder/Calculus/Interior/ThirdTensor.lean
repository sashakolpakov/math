import OAI.Analysis.PDE.Nonlinear.HolderComponents

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Nonlinear

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

local instance interiorTensorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorTensorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorTensorSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorTensorSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorTensorThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorTensorThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- All directional Hessians in an orthonormal basis control the actual
third Fréchet derivative, with a dimension-only loss. -/
theorem third_norm_le_of_directional_hessians
    (b : OrthonormalBasis I ℝ E) (u : E → ℝ) (hu : ContDiff ℝ 3 u)
    (x : E) (M : ℝ)
    (h : ∀ i, ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i))) x‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ (Fintype.card I : ℝ)*M := by
  calc
    _ ≤ ∑ i, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x (b i)‖ :=
      OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis b _
    _ ≤ ∑ _i : I, M := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu] using h i
    _ = _ := by simp

theorem third_difference_le_of_directional_hessians
    (b : OrthonormalBasis I ℝ E) (u : E → ℝ) (hu : ContDiff ℝ 3 u)
    (x y : E) (M : ℝ)
    (h : ∀ i, ‖fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i))) x-
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i))) y‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
      (Fintype.card I : ℝ)*M := by
  calc
    _ ≤ ∑ i, ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y) (b i)‖ := OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis b _
    _ ≤ ∑ _i : I, M := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sub_apply, OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u hu] using h i
    _ = _ := by simp

end OAI.Analysis.PDE.Schauder
