import OAI.Geometry.Nikodym.Abstract.MetricPullback
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] in
theorem chart_inverse_mfderiv_injective (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y) := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy
  have hr : Set.range (𝓘(ℝ,E) : E → E) = Set.univ := Set.range_id
  rw [hr,mfderivWithin_univ] at h
  apply Function.LeftInverse.injective (g :=
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p) ((extChartAt 𝓘(ℝ,E) p).symm y))
  intro u
  exact congrArg (fun A : E →L[ℝ] E => A u) h

/-- The genuine Riemannian metric expressed in an ordinary atlas chart.
The domain is the chart target; coefficients use the actual differential of
the inverse chart, not an assumed local metric model. -/
def abstractChartMetric (p : M) : SmoothCoordinateMetric E where
  domain := (extChartAt 𝓘(ℝ,E) p).target
  isOpen_domain := isOpen_extChartAt_target p
  coefficient := riemannianPullbackOperator (extChartAt 𝓘(ℝ,E) p).symm
  smooth := contDiffOn_riemannianPullbackOperator (isOpen_extChartAt_target p)
    (contMDiffOn_extChartAt_symm p)
  symmetric := by
    intro y hy u v
    conv_rhs => rw [real_inner_comm]
    rw [inner_riemannianPullbackOperator,inner_riemannianPullbackOperator]
    simp only [riemannianPullbackForm_apply]
    exact real_inner_comm _ _
  positive := by
    intro y hy u hu
    rw [inner_riemannianPullbackOperator,riemannianPullbackForm_apply]
    apply real_inner_self_pos.mpr
    intro heq
    apply hu
    apply chart_inverse_mfderiv_injective p hy
    exact heq.trans (ContinuousLinearMap.map_zero _).symm

@[simp] theorem abstractChartMetric_domain (p : M) :
    (abstractChartMetric (E:=E) p).domain = (extChartAt 𝓘(ℝ,E) p).target := rfl

@[simp] theorem abstractChartMetric_inner (p : M) (y u v : E) :
    (abstractChartMetric (E:=E) p).inner y u v =
      ⟪mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y u,
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y v⟫ := by
  exact inner_riemannianPullbackOperator _ _ _ _

theorem abstractChartMetric_base_mem (p : M) :
    extChartAt 𝓘(ℝ,E) p p ∈ (abstractChartMetric (E:=E) p).domain :=
  (extChartAt 𝓘(ℝ,E) p).map_source (mem_extChartAt_source p)

end OAI.Geometry.Nikodym
