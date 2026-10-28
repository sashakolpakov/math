import OAI.Analysis.Fourier.WavePackets.CombinedJet
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.GeometricFamilies

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped ContDiff

variable {Z T E F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def flowPullback (Φ : T × E → E) (f : Z × E → F) (p : (Z × T) × E) : F :=
  f (p.1.1, Φ (p.1.2,p.2))

def flowJacobian (Φ : T × E → E) (J : Z × E → E →L[ℝ] E)
    (p : (Z × T) × E) : E →L[ℝ] E :=
  (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian Φ (p.1.2,p.2)).comp (flowPullback Φ J p)

def flowCurvature (Φ : T × E → E) (J : Z × E → E →L[ℝ] E)
    (K : Z × E → E →L[ℝ] E →L[ℝ] E)
    (p : (Z × T) × E) : E →L[ℝ] E →L[ℝ] E :=
  composeInverseCurvature (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian Φ (p.1.2,p.2))
    (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseHessian Φ (p.1.2,p.2)) (flowPullback Φ J p) (flowPullback Φ K p)

theorem contDiff_flowPullback {Φ : T × E → E} {f : Z × E → F}
    (hΦ : ContDiff ℝ ∞ Φ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (flowPullback Φ f) :=
  hf.comp ((contDiff_fst.fst).prodMk
    (hΦ.comp ((contDiff_fst.snd).prodMk contDiff_snd)))

theorem contDiffOn_flowJacobian {Φ : T × E → E} {I : Set T}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : T × E => OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ I})
    {J : Z × E → E →L[ℝ] E} (hJ : ContDiff ℝ ∞ J) :
    ContDiffOn ℝ ∞ (flowJacobian Φ J) {p : (Z × T) × E | p.1.2 ∈ I} := by
  have hA : ContDiffOn ℝ ∞ (fun p : (Z × T) × E => OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian Φ (p.1.2,p.2))
      {p : (Z × T) × E | p.1.2 ∈ I} :=
    (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_inverseJacobian hI hΦ hi).comp
      ((contDiff_fst.snd).prodMk contDiff_snd).contDiffOn (fun _ hp => hp)
  exact hA.clm_comp (contDiff_flowPullback hΦ hJ).contDiffOn

theorem contDiffOn_flowCurvature {Φ : T × E → E} {I : Set T}
    (hI : IsOpen I) (hΦ : ContDiff ℝ ∞ Φ)
    (hi : ContDiffOn ℝ ∞ (fun p : T × E => OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily Φ p.1 p.2) {p | p.1 ∈ I})
    {J : Z × E → E →L[ℝ] E} (hJ : ContDiff ℝ ∞ J)
    {K : Z × E → E →L[ℝ] E →L[ℝ] E} (hK : ContDiff ℝ ∞ K) :
    ContDiffOn ℝ ∞ (flowCurvature Φ J K) {p : (Z × T) × E | p.1.2 ∈ I} := by
  apply contDiffOn_composeInverseCurvature
  · exact (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_inverseJacobian hI hΦ hi).comp
      ((contDiff_fst.snd).prodMk contDiff_snd).contDiffOn (fun _ hp => hp)
  · exact (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiffOn_inverseHessian hI hΦ hi).comp
      ((contDiff_fst.snd).prodMk contDiff_snd).contDiffOn (fun _ hp => hp)
  · exact (contDiff_flowPullback hΦ hJ).contDiffOn
  · exact (contDiff_flowPullback hΦ hK).contDiffOn

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ T] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem flowPullback_zero {Φ : T × E → E} (hΦ : ∀ x, Φ (0,x) = x)
    (f : Z × E → F) (z : Z) (x : E) : flowPullback Φ f ((z,0),x) = f (z,x) := by
  simp only [flowPullback,hΦ]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ T] in
theorem flowJacobian_zero {Φ : T × E → E} (hΦ : ∀ x, Φ (0,x) = x)
    (J : Z × E → E →L[ℝ] E) (z : Z) (x : E) :
    flowJacobian Φ J ((z,0),x) = J (z,x) := by
  simp only [flowJacobian,OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian_zero hΦ,flowPullback_zero hΦ,ContinuousLinearMap.id_comp]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace ℝ T] in
theorem flowCurvature_zero {Φ : T × E → E} (hΦ : ∀ x, Φ (0,x) = x)
    (J : Z × E → E →L[ℝ] E) (K : Z × E → E →L[ℝ] E →L[ℝ] E) (z : Z) (x : E) :
    flowCurvature Φ J K ((z,0),x) = K (z,x) := by
  ext v w
  simp only [flowCurvature,OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseJacobian_zero hΦ,OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseHessian_zero hΦ,
    flowPullback_zero hΦ,composeInverseCurvature_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add]

end OAI.Analysis.Fourier.WavePackets
