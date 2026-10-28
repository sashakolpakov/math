import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreResidual

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "V" => CoordinateSpace n 4

local instance mooreChartFirstGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] Y) := inferInstance
local instance mooreChartFirstSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] Y) := inferInstance
local instance mooreChartSecondGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
local instance mooreChartSecondSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) := inferInstance

/-- Exact chain rule, valid for only C² functions, for the matrix used in
the finite-dimensional normal bootstrap. -/
theorem mooreChartMatrix_eq_quaternionHessian
    {u₀ : V → ℝ} {u : E → ℝ} {P : V → E} {x : V}
    (h₀ : ContDiffAt ℝ 2 u₀ x) (hu : ContDiffAt ℝ 2 u (P x))
    (hP : ContDiffAt ℝ 2 P x) :
    mooreChartMatrix (fderiv ℝ (fderiv ℝ u₀) x) (fderiv ℝ P x)
      (fderiv ℝ (fderiv ℝ P) x) (fderiv ℝ u (P x)) (fderiv ℝ (fderiv ℝ u) (P x)) =
    quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ u₀ y + u (P y)) x := by
  unfold mooreChartMatrix quaternionHessian realHessian
  congr 1
  funext i j
  have hadd := OAI.Analysis.PDE.Schauder.second_fderiv_add_at h₀ (hu.comp x hP)
  simp only [Function.comp_def] at hadd
  rw [hadd]
  simp only [add_apply]
  congr 1
  exact (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hu hP (coordinateVector i) (coordinateVector j)).symm

theorem fderiv_left_inverse_surjective
    {G : E → V} {P : V → E} {x : E}
    (hG : DifferentiableAt ℝ G x) (hP : DifferentiableAt ℝ P (G x))
    (hi : (fun y ↦ P (G y)) =ᶠ[𝓝 x] id) :
    Function.Surjective (fderiv ℝ P (G x)) := by
  have he : (fderiv ℝ P (G x)).comp (fderiv ℝ G x) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x hP hG]
    simpa only [Function.comp_def,fderiv_id] using hi.fderiv_eq (𝕜 := ℝ)
  intro y
  refine ⟨fderiv ℝ G x y,?_⟩
  exact congrArg (fun L : E →L[ℝ] E ↦ L y) he

end OAI.Analysis.PDE.Dirichlet
