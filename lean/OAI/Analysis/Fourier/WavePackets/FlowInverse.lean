import OAI.Analysis.Fourier.WavePackets.FlowCoefficients

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped ContDiff

variable {Z T E : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def flowInverse (Φ : T × E → E) (Ψ : E → E) (t : T) (y : E) : E :=
  OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ t (Ψ y)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup T] [NormedSpace ℝ T] in
theorem flowJacobian_eq_fderiv
    (Φ : T × E → E) (Ψ : E → E) (J : Z × E → E →L[ℝ] E)
    (z : Z) (t : T) (x y : E) (hpoint : Ψ y = Φ (t,x))
    (hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ t) (Φ (t,x)))
    (hΨ : ContDiffAt ℝ 2 Ψ y) (hJ : J (z,Φ (t,x)) = fderiv ℝ Ψ y) :
    flowJacobian Φ J ((z,t),x) = fderiv ℝ (flowInverse Φ Ψ t) y := by
  have hi' : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ t) (Ψ y) := by
    rw [hpoint]
    exact hi
  unfold flowJacobian flowPullback OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian flowInverse
  rw [hJ]
  symm
  simpa only [hpoint] using fderiv_fun_comp y (hi'.differentiableAt (by norm_num))
    (hΨ.differentiableAt (by norm_num))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup T] [NormedSpace ℝ T] in
theorem flowCurvature_eq_second_fderiv
    (Φ : T × E → E) (Ψ : E → E) (J : Z × E → E →L[ℝ] E)
    (K : Z × E → E →L[ℝ] E →L[ℝ] E)
    (z : Z) (t : T) (x y : E) (hpoint : Ψ y = Φ (t,x))
    (hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ t) (Φ (t,x)))
    (hΨ : ContDiffAt ℝ 2 Ψ y) (hJ : J (z,Φ (t,x)) = fderiv ℝ Ψ y)
    (hK : K (z,Φ (t,x)) = fderiv ℝ (fderiv ℝ Ψ) y) :
    flowCurvature Φ J K ((z,t),x) = fderiv ℝ (fderiv ℝ (flowInverse Φ Ψ t)) y := by
  have hi' : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ t) (Ψ y) := by
    rw [hpoint]
    exact hi
  unfold flowCurvature flowPullback OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseHessian flowInverse
  rw [hJ,hK]
  symm
  simpa only [hpoint] using second_fderiv_comp_eq_composeInverseCurvature hi' hΨ

end OAI.Analysis.Fourier.WavePackets
