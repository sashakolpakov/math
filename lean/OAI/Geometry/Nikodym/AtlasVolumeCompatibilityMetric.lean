import OAI.Geometry.Nikodym.Abstract.Metric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Bundle Manifold
open scoped Topology ContDiff RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

def atlasTransition (p q : M) : E → E :=
  extChartAt 𝓘(ℝ,E) q ∘ (extChartAt 𝓘(ℝ,E) p).symm

def atlasTransitionDomain (p q : M) : Set E :=
  (extChartAt 𝓘(ℝ,E) p).target ∩
    (extChartAt 𝓘(ℝ,E) p).symm ⁻¹' (extChartAt 𝓘(ℝ,E) q).source

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] in
theorem isOpen_atlasTransitionDomain (p q : M) :
    IsOpen (atlasTransitionDomain (E:=E) p q) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] in
theorem contDiffOn_atlasTransition (p q : M) :
    ContDiffOn ℝ ∞ (atlasTransition (E:=E) p q) (atlasTransitionDomain (E:=E) p q) :=
  contDiffOn_ext_coord_change q p

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] in
theorem atlasTransition_hasFDerivAt (p q : M) {y : E}
    (hy : y ∈ atlasTransitionDomain (E:=E) p q) :
    HasFDerivAt (atlasTransition (E:=E) p q)
      (fderiv ℝ (atlasTransition (E:=E) p q) y) y :=
  ((contDiffOn_atlasTransition p q).differentiableOn (by simp) y hy).differentiableAt
    ((isOpen_atlasTransitionDomain p q).mem_nhds hy) |>.hasFDerivAt

omit [FiniteDimensional ℝ E] [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] in
/-- The inverse-chart differential cancels the true coordinate-transition
Jacobian. This is the chain rule for the actual atlas, not a metric premise. -/
theorem atlasTransition_inverse_mfderiv (p q : M) {y : E}
    (hy : y ∈ atlasTransitionDomain (E:=E) p q) (v : E) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) q).symm
        (atlasTransition (E:=E) p q y)
        (fderiv ℝ (atlasTransition (E:=E) p q) y v) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y v := by
  have hp := (mdifferentiableOn_extChartAt_symm (I:=𝓘(ℝ,E)) (x:=p) y hy.1).mdifferentiableAt
    ((isOpen_extChartAt_target p).mem_nhds hy.1)
  have hqy : (extChartAt 𝓘(ℝ,E) p).symm y ∈ (extChartAt 𝓘(ℝ,E) q).source := hy.2
  have hq := mdifferentiableAt_extChartAt (I:=𝓘(ℝ,E)) (x:=q)
    (y:=(extChartAt 𝓘(ℝ,E) p).symm y)
    (by simpa only [extChartAt_source] using hqy)
  have hc : fderiv ℝ (atlasTransition (E:=E) p q) y =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) q)
        ((extChartAt 𝓘(ℝ,E) p).symm y)).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp y hq hp
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I:=𝓘(ℝ,E)) hqy
  have hr : Set.range (𝓘(ℝ,E) : E → E) = Set.univ := Set.range_id
  rw [hr, mfderivWithin_univ] at hi
  rw [hc]
  exact congrArg (fun A => A
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm y v)) hi

/-- The two actual pulled-back metric tensors obey the coordinate Jacobian law. -/
theorem abstractChartMetric_transition_inner (p q : M) {y : E}
    (hy : y ∈ atlasTransitionDomain (E:=E) p q) (u v : E) :
    (abstractChartMetric (E:=E) p).inner y u v =
      (abstractChartMetric (E:=E) q).inner (atlasTransition (E:=E) p q y)
        (fderiv ℝ (atlasTransition (E:=E) p q) y u)
        (fderiv ℝ (atlasTransition (E:=E) p q) y v) := by
  rw [abstractChartMetric_inner, abstractChartMetric_inner]
  have hpoint : (extChartAt 𝓘(ℝ,E) q).symm (atlasTransition (E:=E) p q y) =
      (extChartAt 𝓘(ℝ,E) p).symm y :=
    (extChartAt 𝓘(ℝ,E) q).left_inv hy.2
  rw [atlasTransition_inverse_mfderiv p q hy u, atlasTransition_inverse_mfderiv p q hy v]
  rw [hpoint]

end OAI.Geometry.Nikodym
