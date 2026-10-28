import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveGluing
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence

/-! # Berry Gauge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryGauge.CM.Construction

noncomputable section

section

/-! The actual normalized Berry connection supplies local primitives
of the projective Kähler form on the standard projective cover. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : Type} [Fintype ι]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

def projectiveBerryLocal (i : ι) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw _ (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i))
    (ManifoldMetric.CM.Construction.manifoldLiftBerry_smooth (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i).isOpen _ (hhol i)
      (ProjectiveGluing.CM.Construction.projectiveLift_nonzero p hp i))

theorem projectiveBerryLocal_d (i : ι) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (projectiveBerryLocal p hp hhol i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i) (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [projectiveBerryLocal, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_ofRaw_apply]
  exact (ProjectiveGluing.CM.Construction.projectiveCurvatureRaw_eq p hp hhol i x.property).symm

def projectiveBerryPrimitive (i : ι) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i) 1 :=
  Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1 (projectiveBerryLocal p hp hhol i)

theorem projectiveBerryPrimitive_d (i : ι) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveBerryPrimitive p hp hhol i) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Subtype.val : ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i → M)
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))
        (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol) := by
  rw [projectiveBerryPrimitive, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, projectiveBerryLocal_d,
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]

theorem manifoldLiftBerry_inChart_apply
    {U : Set M} (hU : IsOpen U) (f : M → ι → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    {z : E} (hz : z ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) (v : Fin 1 → E) :
    (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) f).inChart e z v =
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (f (e.symm z))
        (fderiv ℂ (f ∘ e.symm) z).toLinearMap (v 0) : ℂ) := by
  have hreal := ManifoldMetric.CM.Construction.manifoldLift_realSmooth hU f hf
  have hd := ((hreal (e.symm z) hz.2).contMDiffAt (hU.mem_nhds hz.2)).mdifferentiableAt (by simp)
  rw [ManifoldMetric.CM.Construction.manifoldLiftBerry, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_inChart _ f e
    (OpenPartialHomeomorph.refl (ι → ℂ)) he (by simp) hz.1 (by trivial) hd]
  simp only [ManifoldMetric.CM.Construction.homogeneousManifoldBerry, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.toNormedSpace_toManifold, OpenPartialHomeomorph.refl_apply,
    Function.id_comp, id_eq]
  rw [((ManifoldMetric.CM.Construction.manifoldLift_inChart_holomorphic hU f hf e he hz).differentiableAt
    (by simp)).fderiv_restrictScalars ℝ]
  change HomogeneousMetric.CM.Construction.homogeneousBerryCovector (f (e.symm z)) (fderiv ℂ (f ∘ e.symm) z (v 0)) = _
  rw [HomogeneousMetric.CM.Construction.homogeneousBerryCovector_apply]
  rfl

end

/-! The actual local projective connection changes by the normalized
imaginary logarithmic derivative of the rescaling function. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : Type} [Fintype ι]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem manifoldLiftBerry_gauge_inChart
    {U : Set M} (hU : IsOpen U) (f g : M → ι → ℂ) (a : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ g U)
    (ha : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ a U)
    (hng : ∀ x ∈ U, g x ≠ 0) (hna : ∀ x ∈ U, a x ≠ 0)
    (hfg : ∀ x ∈ U, f x = a x • g x)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    {z : E} (hz : z ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e U) (v : Fin 1 → E) :
    (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) f).inChart e z v -
      (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) g).inChart e z v =
      ((fderiv ℂ (a ∘ e.symm) z (v 0) / a (e.symm z)).im / (2 * Real.pi) : ℝ) := by
  rw [manifoldLiftBerry_inChart_apply hU f hf e he hz,
    manifoldLiftBerry_inChart_apply hU g hg e he hz]
  have hga := ManifoldMetric.CM.Construction.manifoldLift_inChart_holomorphic hU g hg e he hz
  have haa : ContDiffAt ℂ ∞ (a ∘ e.symm) z :=
    (((ha (e.symm z) hz.2).contMDiffAt (hU.mem_nhds hz.2)).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hz.1)).contDiffAt
  have hloc : f ∘ e.symm =ᶠ[𝓝 z] (a ∘ e.symm) • (g ∘ e.symm) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.Algebra.isOpen_manifoldFormChartDomain e hU).mem_nhds hz] with w hw
    exact hfg _ hw.2
  have hD : (fderiv ℂ (f ∘ e.symm) z).toLinearMap =
      a (e.symm z) • (fderiv ℂ (g ∘ e.symm) z).toLinearMap +
      (fderiv ℂ (a ∘ e.symm) z).toLinearMap.smulRight (g (e.symm z)) := by
    rw [hloc.fderiv_eq]
    exact congrArg ContinuousLinearMap.toLinearMap
      (fderiv_smul (haa.differentiableAt (by simp)) (hga.differentiableAt (by simp)))
  rw [hfg _ hz.2, hD, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection_gauge
    (a (e.symm z)) (hna _ hz.2) (g (e.symm z)) (hng _ hz.2), Complex.ofReal_add]
  exact add_sub_cancel_left _ _

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem logarithmic_derivative_of_exp
    {l : E → ℂ} {z : E} (hl : DifferentiableAt ℂ l z) (u : E) :
    fderiv ℂ (fun w => Complex.exp (l w)) z u / Complex.exp (l z) = fderiv ℂ l z u := by
  rw [hl.hasFDerivAt.cexp.fderiv]
  change (Complex.exp (l z) * fderiv ℂ l z u) / Complex.exp (l z) = _
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryGauge.CM.Construction
