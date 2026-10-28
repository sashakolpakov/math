import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.InverseJets

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set
open scoped ContDiff

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Second derivative of the composition of two inverse coordinate maps. -/
def composeInverseCurvature
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (J : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E E E).flip J).comp (B.comp J) +
    ((ContinuousLinearMap.compL ℝ E E E) A).comp K

@[simp] theorem composeInverseCurvature_apply
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (J : E →L[ℝ] E) (K : E →L[ℝ] E →L[ℝ] E) (v w : E) :
    composeInverseCurvature A B J K v w = B (J v) (J w) + A (K v w) := rfl

theorem contDiffOn_composeInverseCurvature {S : Set Y} {q : ℕ∞ω}
    {A J : Y → E →L[ℝ] E} {B K : Y → E →L[ℝ] E →L[ℝ] E}
    (hA : ContDiffOn ℝ q A S) (hB : ContDiffOn ℝ q B S)
    (hJ : ContDiffOn ℝ q J S) (hK : ContDiffOn ℝ q K S) :
    ContDiffOn ℝ q (fun p => composeInverseCurvature (A p) (B p) (J p) (K p)) S := by
  have hleft := (ContinuousLinearMap.compL ℝ E E E).flip.contDiff.comp_contDiffOn hJ
  have hright := hB.clm_comp hJ
  have hpost := (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn hA
  exact (hleft.clm_comp hright).add (hpost.clm_comp hK)

theorem second_fderiv_comp_eq_composeInverseCurvature
    {f g : E → E} {x : E} (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f (g y))) x =
      composeInverseCurvature (fderiv ℝ f (g x)) (fderiv ℝ (fderiv ℝ f) (g x))
        (fderiv ℝ g x) (fderiv ℝ (fderiv ℝ g) x) := by
  ext v w
  exact OAI.Analysis.PDE.Elliptic.second_fderiv_comp hf hg v w

end OAI.Analysis.Fourier.WavePackets
