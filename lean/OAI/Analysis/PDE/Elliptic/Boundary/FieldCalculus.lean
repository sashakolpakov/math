import OAI.Analysis.PDE.Dirichlet.AffineField
import OAI.Analysis.PDE.Elliptic.Boundary.PullbackBounds

/-! Exact second-order commutator for a variable tangent vector field. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet InnerProductSpace

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fieldDerivative (u : E → ℝ) (T : E → E) (x : E) : ℝ := fderiv ℝ u x (T x)

theorem contDiff_fieldDerivative {u : E → ℝ} {T : E → E} {m n : WithTop ENat}
    (hu : ContDiff ℝ n u) (hT : ContDiff ℝ m T) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (fieldDerivative u T) :=
  (hu.fderiv_right hmn).clm_apply hT

theorem directionalDerivative_fieldDerivative {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 2 u) (hT : Differentiable ℝ T) (v x : E) :
    OAI.Analysis.PDE.Dirichlet.directionalDerivative (fieldDerivative u T) v x =
      fderiv ℝ u x (fderiv ℝ T x v) + fderiv ℝ (fderiv ℝ u) x v (T x) := by
  unfold OAI.Analysis.PDE.Dirichlet.directionalDerivative fieldDerivative
  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x) (hT x)]
  rfl

theorem hessian_fieldDerivative {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) (v w x : E) :
    fderiv ℝ (fderiv ℝ (fieldDerivative u T)) x v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w (T x) +
      fderiv ℝ (fderiv ℝ u) x v (fderiv ℝ T x w) +
      fderiv ℝ (fderiv ℝ u) x w (fderiv ℝ T x v) +
      fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x v w) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hf : ContDiff ℝ 2 (fieldDerivative u T) := contDiff_fieldDerivative hu hT (by norm_num)
  have hD1 := (hu.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hD2 := ((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDT := (hT.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hP : Differentiable ℝ (fun y => fderiv ℝ (fderiv ℝ u) y w) :=
    hD2.clm_apply (differentiable_const w)
  have hQ : Differentiable ℝ (fun y => fderiv ℝ T y w) :=
    hDT.clm_apply (differentiable_const w)
  have hfirst : OAI.Analysis.PDE.Dirichlet.directionalDerivative (fieldDerivative u T) w =
      fun y => fderiv ℝ u y (fderiv ℝ T y w) + fderiv ℝ (fderiv ℝ u) y w (T y) :=
    funext (directionalDerivative_fieldDerivative hu2 (hT.differentiable (by norm_num)) w)
  have hconst : fderiv ℝ (fun _ : E => w) x = 0 := by
    simp
  rw [← OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hf v w x, hfirst]
  unfold OAI.Analysis.PDE.Dirichlet.directionalDerivative
  have hadd : fderiv ℝ (fun y => fderiv ℝ u y (fderiv ℝ T y w) +
      fderiv ℝ (fderiv ℝ u) y w (T y)) x =
      fderiv ℝ (fun y => fderiv ℝ u y (fderiv ℝ T y w)) x +
      fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y w (T y)) x :=
    (((hD1 x).clm_apply (hQ x)).hasFDerivAt.add
      ((hP x).clm_apply (hT.differentiable (by norm_num) x)).hasFDerivAt).fderiv
  rw [hadd,
    fderiv_clm_apply (hD1 x) (hQ x), fderiv_clm_apply (hP x) (hT.differentiable (by norm_num) x),
    fderiv_clm_apply (hDT x) (differentiableAt_const w),
    fderiv_clm_apply (hD2 x) (differentiableAt_const w)]
  simp only [hconst, ContinuousLinearMap.comp_zero, zero_add, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  simp [add_comm, add_left_comm, add_assoc]

end Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hessianOperator_fieldDerivative {u : E → ℝ} {T : E → E}
    (hu : ContDiff ℝ 3 u) (hT : ContDiff ℝ 2 T) (x : E) :
    fderiv ℝ (gradient (fieldDerivative u T)) x =
      fderiv ℝ (gradient (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (T x))) x +
      (fderiv ℝ T x).adjoint.comp (fderiv ℝ (gradient u) x) +
      (fderiv ℝ (gradient u) x).comp (fderiv ℝ T x) +
      fderiv ℝ (gradient (fun y => fderiv ℝ u x (T y))) x := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hf := contDiff_fieldDerivative hu hT (m := 2) (by norm_num)
  have hd := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) (T x)
  have hl : ContDiff ℝ 2 (fun y => fderiv ℝ u x (T y)) := (fderiv ℝ u x).contDiff.comp hT
  ext v
  apply ext_inner_right ℝ
  intro w
  simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_left]
  rw [inner_fderiv_gradient_at hf.contDiffAt, hessian_fieldDerivative hu hT,
    inner_fderiv_gradient_at hd.contDiffAt, OAI.Analysis.PDE.Dirichlet.hessian_directionalDerivative hu,
    ContinuousLinearMap.adjoint_inner_left,
    inner_fderiv_gradient_at hu2.contDiffAt, inner_fderiv_gradient_at hu2.contDiffAt,
    inner_fderiv_gradient_at hl.contDiffAt, second_fderiv_linear_comp _ hT.contDiffAt]
  rw [(hu2.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (fderiv ℝ T x v) w]

end OAI.Analysis.PDE.Elliptic
