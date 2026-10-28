import OAI.Analysis.PDE.Dirichlet.RealOperator
import OAI.Analysis.PDE.Elliptic.HessianNorm
import OAI.Analysis.PDE.Elliptic.RescaleMeasure

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def rescalePotential (f : E → ℝ) (z : E) (R : ℝ) (x : E) : ℝ :=
  (R ^ 2)⁻¹ • f (OAI.Analysis.PDE.Elliptic.rescalePoint z R x)

omit [FiniteDimensional ℝ E] in
theorem contDiff_rescalePotential {f : E → ℝ} {k : WithTop ENat}
    (hf : ContDiff ℝ k f) (z : E) (R : ℝ) :
    ContDiff ℝ k (rescalePotential f z R) :=
  (hf.comp ((OAI.Analysis.PDE.Elliptic.rescalePoint_contDiff z R).of_le le_top)).const_smul _

theorem fderiv_gradient_smul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    fderiv ℝ (gradient (fun y ↦ c • f y)) x = c • fderiv ℝ (gradient f) x := by
  have hg : gradient (fun y ↦ c • f y) = fun y ↦ c • gradient f y := by
    funext y
    have hd : fderiv ℝ (fun y ↦ c • f y) y = c • fderiv ℝ f y :=
      (((hf.differentiable (by norm_num)) y).hasFDerivAt.const_smul c).fderiv
    change (toDual ℝ E).symm (fderiv ℝ (fun y ↦ c • f y) y) =
      c • (toDual ℝ E).symm (fderiv ℝ f y)
    rw [hd, map_smul]
  rw [hg]
  exact ((OAI.Analysis.PDE.Elliptic.differentiable_gradient hf x).hasFDerivAt.const_smul c).fderiv

theorem fderiv_gradient_rescalePotential {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    fderiv ℝ (gradient (rescalePotential f z R)) x =
      fderiv ℝ (gradient f) (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) := by
  unfold rescalePotential
  have hcomp : ContDiff ℝ 2 (fun y ↦ f (OAI.Analysis.PDE.Elliptic.rescalePoint z R y)) :=
    hf.comp ((OAI.Analysis.PDE.Elliptic.rescalePoint_contDiff z R).of_le le_top)
  rw [fderiv_gradient_smul hcomp,
    OAI.Analysis.PDE.Elliptic.fderiv_gradient_rescalePoint hf, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hR), one_smul]

theorem second_fderiv_rescalePotential {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (rescalePotential f z R)) x =
      fderiv ℝ (fderiv ℝ f) (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) := by
  ext u v
  rw [← OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient (contDiff_rescalePotential hf z R),
    fderiv_gradient_rescalePotential hf z hR, OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hf]

theorem quaternionHessian_rescalePotential {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f)
    (z : CoordinateSpace n s) {R : ℝ} (hR : R ≠ 0) (x : CoordinateSpace n s) :
    quaternionHessian e (rescalePotential f z R) x =
      quaternionHessian e f (OAI.Analysis.PDE.Elliptic.rescalePoint z R x) := by
  unfold quaternionHessian realHessian
  rw [second_fderiv_rescalePotential hf z hR]

end OAI.Analysis.PDE.Dirichlet
