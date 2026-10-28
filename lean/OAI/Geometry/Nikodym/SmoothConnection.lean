import OAI.Geometry.Nikodym.SmoothMetric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def adjointRealCLM : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := by intros; simp
  map_smul' := by intros; simp
  cont := ContinuousLinearMap.adjoint.continuous

theorem contDiff_metricKoszulVector :
    ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) =>
      metricKoszulVector p.1 p.2.1 p.2.2) := by
  have hf : ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) =>
      (ContinuousLinearMap.flipₗᵢ ℝ E E E p.1) p.2.1) := by fun_prop
  have ha : ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) =>
      adjointRealCLM ((ContinuousLinearMap.flipₗᵢ ℝ E E E p.1) p.2.1) p.2.2) := by
    have hs : ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) => p.2.2) := by fun_prop
    exact ((adjointRealCLM (E := E)).contDiff.comp hf).clm_apply hs
  change ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) =>
    (1/2 : ℝ) • (p.1 p.2.1 p.2.2 + p.1 p.2.2 p.2.1 -
      adjointRealCLM ((ContinuousLinearMap.flipₗᵢ ℝ E E E p.1) p.2.1) p.2.2))
  exact ((by fun_prop : ContDiff ℝ ∞ (fun p : (E →L[ℝ] E →L[ℝ] E) × (E × E) =>
    p.1 p.2.1 p.2.2 + p.1 p.2.2 p.2.1)).sub ha).const_smul (1/2 : ℝ)

namespace SmoothCoordinateMetric

variable (g : SmoothCoordinateMetric E)

/-- Smoothness of the Levi-Civita Christoffel expression is derived from
the smooth metric and pointwise positivity, without any connection premise. -/
theorem contDiffAt_christoffel {x : E} (hx : x ∈ g.domain) (u v : E) :
    ContDiffAt ℝ ∞ (fun p : E × (E × E) => g.christoffel p.1 p.2.1 p.2.2) (x,u,v) := by
  have hg : ContDiffAt ℝ ∞ g.coefficient x :=
    (g.smooth x hx).contDiffAt (g.isOpen_domain.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ g.coefficient) x :=
    hg.fderiv_right (by simp)
  have hi : ContDiffAt ℝ ∞ (fun x => (g.coefficient x).inverse) x :=
    (g.invertible hx).contDiffAt_map_inverse.comp x hg
  have hk : ContDiffAt ℝ ∞ (fun p : E × (E × E) =>
      metricKoszulVector (fderiv ℝ g.coefficient p.1) p.2.1 p.2.2) (x,u,v) :=
    contDiff_metricKoszulVector.contDiffAt.comp _
      ((hD.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  exact (hi.comp _ contDiffAt_fst).clm_apply hk

def geodesicSpray (p : E × E) : E × E := (p.2,-g.christoffel p.1 p.2 p.2)

theorem contDiffAt_geodesicSpray {p : E × E} (hp : p.1 ∈ g.domain) :
    ContDiffAt ℝ ∞ g.geodesicSpray p := by
  have hc := (g.contDiffAt_christoffel hp p.2 p.2).comp p
    (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  exact contDiffAt_snd.prodMk hc.neg

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
