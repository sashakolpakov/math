import OAI.AlgebraicGeometry.Picard.ThetaConstruction.LogarithmicChange
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ManifoldMetric
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic

/-! # Connection Pullback Change -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ConnectionPullbackChange.Geometric

noncomputable section

/-! Pulled-back torus connections obey the differential change law for
every actual holomorphic logarithm of their theta transition. -/

open Filter _root_.Topology Set
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) (hP : matrix.transpose = -matrix)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℂ A]
    [IsScalarTower ℝ ℂ A] [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℂ, A) ∞ B]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem thetaTorusConnection_pullback_logarithmic_change (hdeg : V.degree = U.degree + 1)
    (i j : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (h : B → (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) (l : B → ℂ)
    (hh : ContMDiff 𝓘(ℂ, A) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) ∞ h)
    (hl : ContMDiff 𝓘(ℂ, A) 𝓘(ℂ, ℂ) ∞ l)
    (hi : ∀ x, h x ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V i)
    (hj : ∀ x, h x ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V j)
    (hexp : ∀ x w, (QuotientAddGroup.mk w : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) = h x →
      Complex.exp (l x) = RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 w) :
    ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V j).pullback h -
      ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback h =
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm l (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hl))).val := by
  funext x
  let e := chartAt A x
  let k := h x
  let c := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart k
  have he : e ∈ atlas A B := chart_mem_atlas A x
  have hx : x ∈ e.source := mem_chart_source A x
  have hy : e x ∈ e.target := e.map_source hx
  have hcx : h (e.symm (e x)) ∈ c.source := by
    rw [e.left_inv hx]
    exact (ProjectivePeriodData.Geometric.projectivePeriodData F).mem_periodChart_source k
  let L : A → (ProjectivePeriodData.Geometric.projectivePeriodData F).space := c ∘ h ∘ e.symm
  have hL : ContDiffAt ℂ ∞ L (e x) := by
    have hc : ContMDiffAt 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) ∞ c (h (e.symm (e x))) :=
      (contMDiffOn_chart (I := 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)) (x := k)).contMDiffAt
        (c.open_source.mem_nhds hcx)
    exact ((hc.comp _ (hh _)).comp _
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy)).contDiffAt
  have hlog : ContDiffAt ℂ ∞ (l ∘ e.symm) (e x) :=
    ((hl _).comp _ (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy)).contDiffAt
  have hmem (a : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
      (ha : ∀ x, h x ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V a) : L (e x) ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V a :=
    ((TorusTheta.Geometric.thetaTorusFrameOpen_chart F) hP U V a k _ hcx).mpr (ha _)
  have hnear : (fun y => Complex.exp ((l ∘ e.symm) y)) =ᶠ[𝓝 (e x)]
      (fun y => RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V j.1 j.2 (L y) / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V i.1 i.2 (L y)) := by
    have hcont := (hh (e.symm (e x))).continuousAt.comp (e.continuousAt_symm hy)
    filter_upwards [hcont.preimage_mem_nhds (c.open_source.mem_nhds hcx)] with y hcy
    apply hexp (e.symm y) (L y)
    have hc := c.left_inv hcy
    rw [(ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_symm] at hc
    exact hc
  have hchange := (LogarithmicChange.Geometric.thetaConnectionRaw_logarithmic_change F) hP U V i j L (l ∘ e.symm) (e x)
    (hL.differentiableAt (by simp)) (hlog.differentiableAt (by simp)) (hmem i hi) (hmem j hj) hnear
  have hchart (a : RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
      (ha : ∀ x, h x ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V a) :
      (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V a).pullback h).inChart e (e x) =
        ((TorusTheta.Geometric.thetaTorusConnectionCoefficients F) hP U V a (L (e x))).compContinuousLinearMap
          (fderiv ℝ L (e x)) := by
    have hp := ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V a).pullback_inChart h e c he
      ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart_mem_atlas k) hy hcx
      ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hh).mdifferentiableAt (by simp))
    have ht : c.symm (c (h (e.symm (e x)))) ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V a :=
      (congrArg (fun q => q ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V a) (c.left_inv hcx)).mpr (ha _)
    have hc := (TorusTheta.Geometric.thetaTorusConnectionRaw_inChart F) hP U V hdeg a k
      (c (h (e.symm (e x)))) (c.map_source hcx) ht
    exact hp.trans (congrArg (fun b : Analysis.DifferentialForms.Manifold.Basic.FormValue (ProjectivePeriodData.Geometric.projectivePeriodData F).space 1 =>
      b.compContinuousLinearMap (fderiv ℝ L (e x))) hc)
  apply ComplexMultiplication.HodgeComparison.ManifoldMetric.CM.Construction.rawManifoldForm_eq_at_of_inChart_eq _ _ e he x hx
  change ((((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V j).pullback h -
    ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback h).inChart e (e x)) = _
  have hsub : (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V j).pullback h -
      ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback h).inChart e (e x) =
      (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V j).pullback h).inChart e (e x) -
        (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V i).pullback h).inChart e (e x) := by
    ext v
    rfl
  rw [hsub, hchart j hj, hchart i hi]
  refine hchange.trans ?_
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hy]
  change _ = extDeriv ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar l).inChart e) (e x)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
  rfl

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ConnectionPullbackChange.Geometric
