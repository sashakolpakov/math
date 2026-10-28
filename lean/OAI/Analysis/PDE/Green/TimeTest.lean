import OAI.Analysis.PDE.Green.PencilIntegral

/-! Actual Hessians of test functions depending only on the extended time block. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem second_fderiv_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ 2 f) (x a b : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (L y))) x a b =
      fderiv ℝ (fderiv ℝ f) (L x) (L a) (L b) := by
  have hfL : ContDiff ℝ 2 (fun y => f (L y)) := hf.comp L.contDiff
  have hfirst : (fun y => fderiv ℝ (fun z => f (L z)) y b) =
      fun y => fderiv ℝ f (L y) (L b) := by
    funext y
    have h := congrArg (fun Q : E →L[ℝ] ℝ => Q b)
      (fderiv_comp y (hf.differentiable (by norm_num) (L y)) L.differentiableAt)
    simpa [Function.comp_def] using h
  have hg : ContDiff ℝ 1 (fun z => fderiv ℝ f z (L b)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  calc
    _ = fderiv ℝ (fun y => fderiv ℝ (fun z => f (L z)) y b) x a :=
      (directional_twice hfL a b x).symm
    _ = fderiv ℝ (fun y => fderiv ℝ f (L y) (L b)) x a := by rw [hfirst]
    _ = fderiv ℝ (fun z => fderiv ℝ f z (L b)) (L x) (L a) := by
      simpa [Function.comp_def] using congrArg (fun Q : E →L[ℝ] ℝ => Q a)
        (fderiv_comp x (hg.differentiable (by norm_num) (L x)) L.differentiableAt)
    _ = _ := directional_twice hf (L a) (L b) (L x)

def timeProjectionLinear (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s where
  toFun x := WithLp.toLp 2 (fun p => x (0, p.2))
  map_add' x y := by ext p; rfl
  map_smul' c x := by ext p; rfl

def timeProjection (n s : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s :=
  (timeProjectionLinear n s).toContinuousLinearMap

theorem timeProjection_coordinate_zero (n s : ℕ) (α : Fin s) :
    timeProjection n s (OAI.Analysis.PDE.Dirichlet.coordinateVector (0, α)) = OAI.Analysis.PDE.Dirichlet.coordinateVector (0, α) := by
  ext p
  obtain ⟨p, β⟩ := p
  have hp : p = 0 := Fin.eq_zero p
  subst p
  simp [timeProjection, timeProjectionLinear, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply]

theorem timeProjection_coordinate_succ (n s : ℕ) (i : Fin n) (α : Fin s) :
    timeProjection n s (OAI.Analysis.PDE.Dirichlet.coordinateVector (i.succ, α)) = 0 := by
  ext p
  simp [timeProjection, timeProjectionLinear, OAI.Analysis.PDE.Dirichlet.coordinateVector]

theorem quaternionHessian_time_zero_zero {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x 0 0 =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e η (timeProjection n s x) 0 0 := by
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.PDE.Dirichlet.realHessian,
    second_fderiv_comp_linear (timeProjection n s) hη, timeProjection_coordinate_zero]

theorem quaternionHessian_time_succ_row {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (i : Fin n) (j : Fin (n + 1)) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x i.succ j = 0 := by
  simp [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.PDE.Dirichlet.realHessian,
    second_fderiv_comp_linear (timeProjection n s) hη, timeProjection_coordinate_succ]

theorem quaternionHessian_time_succ_col {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (i : Fin (n + 1)) (j : Fin n) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x i j.succ = 0 := by
  simp [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.PDE.Dirichlet.realHessian,
    second_fderiv_comp_linear (timeProjection n s) hη, timeProjection_coordinate_succ]

/-- A time-only test has exactly one quaternionic Hessian entry, its ordinary
Euclidean Laplacian. This includes the three-slot extended time of the paper. -/
theorem quaternionHessian_time_only {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x =
      Laplacian.laplacian η (timeProjection n s x) • OAI.LinearAlgebra.Moore.coordinateProjector (n + 1) 0 := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [quaternionHessian_time_zero_zero e hη]
      have ht := OAI.Analysis.PDE.Dirichlet.quaternionHessian_trace e he hη.contDiffAt (x := timeProjection n s x)
      simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_one] at ht
      rw [ht]
      ext <;> simp [OAI.LinearAlgebra.Moore.coordinateProjector]
    · rw [quaternionHessian_time_succ_col e hη]
      simp [OAI.LinearAlgebra.Moore.coordinateProjector]
  · rw [quaternionHessian_time_succ_row e hη]
    simp [OAI.LinearAlgebra.Moore.coordinateProjector]

theorem realTrace_mul_time_test {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x) =
      Laplacian.laplacian η (timeProjection n s x) * (A 0 0).re := by
  rw [quaternionHessian_time_only e he hη, Matrix.mul_smul,
    OAI.LinearAlgebra.Moore.realTrace_smul, OAI.LinearAlgebra.Moore.realTrace_mul_coordinate]

theorem mooreCofactor_normal_of_spatial_posSemidef {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)) (hA : A.IsHermitian)
    (hD : (OAI.LinearAlgebra.Moore.complexify (A.submatrix Fin.succ Fin.succ)).PosSemidef) :
    (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1) A 0 0).re = OAI.LinearAlgebra.Moore.mooreDet n (A.submatrix Fin.succ Fin.succ) := by
  have h := OAI.LinearAlgebra.Moore.mooreCofactor_hermitianBlock_normal_posSemidef (A 0 0).re
    (fun i => A i.succ 0) (A.submatrix Fin.succ Fin.succ) hD
  rw [← OAI.LinearAlgebra.Moore.hermitianBlock_reconstruct A hA] at h
  exact h

/-- The differential paired with an actual time test is its Laplacian times
the determinant of the spatial block, including a semidefinite endpoint. -/
theorem mooreDifferential_time_test {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hη : ContDiff ℝ 2 η)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)) (hA : A.IsHermitian)
    (hD : (OAI.LinearAlgebra.Moore.complexify (A.submatrix Fin.succ Fin.succ)).PosSemidef)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
    OAI.LinearAlgebra.Moore.mooreDifferential (n + 1) A
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x) =
      Laplacian.laplacian η (timeProjection n s x) *
        OAI.LinearAlgebra.Moore.mooreDet n (A.submatrix Fin.succ Fin.succ) := by
  have ht : ContDiff ℝ 2 (fun y => η (timeProjection n s y)) :=
    hη.comp (timeProjection n s).contDiff
  rw [← OAI.LinearAlgebra.Moore.mooreCofactor_pairing (n + 1) A _ (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e ht.contDiffAt),
    realTrace_mul_time_test e he hη, mooreCofactor_normal_of_spatial_posSemidef A hA hD]

end OAI.Analysis.PDE.Green
