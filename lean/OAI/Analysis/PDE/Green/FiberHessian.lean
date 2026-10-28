import OAI.Analysis.PDE.Green.FiberCoordinates

/-! Spatial restrictions of the actual quaternionic Hessian. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

theorem second_fderiv_comp_affine
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (c : F) {f : F → ℝ} (hf : ContDiff ℝ 2 f) (x a b : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (c + L y))) x a b =
      fderiv ℝ (fderiv ℝ f) (c + L x) (L a) (L b) := by
  have hg : ContDiff ℝ 2 (fun z => f (c + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [second_fderiv_comp_linear L hg]
  have hfirst : fderiv ℝ (fun z => f (c + z)) = fun z => fderiv ℝ f (c + z) :=
    funext (fun z => fderiv_comp_add_left c)
  rw [hfirst, fderiv_comp_add_left]

theorem spatialInjection_coordinate (n s : ℕ) (i : Fin n) (α : Fin s) :
    spatialInjection n s (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, α)) = OAI.Analysis.PDE.Dirichlet.coordinateVector (i.succ, α) := by
  ext ⟨j, β⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [spatialInjection, spatialInjectionLinear, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply]
  · simp [spatialInjection, spatialInjectionLinear, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply]

/-- Restriction to a fixed extended time gives exactly the spatial Hessian block. -/
theorem quaternionHessian_fiberEmbedding {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hf : ContDiff ℝ 2 f)
    (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun x => f (fiberEmbedding n s z x)) y =
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f (fiberEmbedding n s z y)).submatrix Fin.succ Fin.succ := by
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.PDE.Dirichlet.realHessian, fiberEmbedding,
    second_fderiv_comp_affine (spatialInjection n s) (timeInjection n s z) hf,
    spatialInjection_coordinate, Matrix.submatrix_apply]

end OAI.Analysis.PDE.Green
