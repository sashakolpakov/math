import OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients

/-! # Covector Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair

noncomputable section

/-! The actual projective metric as a positive Hermitian pairing on each tangent covector fiber. -/

open scoped _root_.Manifold ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions

section Model

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem formMetricPair_add_left (n : ℕ) (a b c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (a + b) c = Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a c + Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n b c := by
  unfold Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair
  rw [map_add]
  exact Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair_add_left _ _ _ _

theorem formMetricPair_smul_left (n : ℕ) (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (z • a) b = conj z * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a b := by
  unfold Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair
  rw [map_smul]
  exact Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair_smul_left _ _ _ z

theorem formMetricPair_smul_right (n : ℕ) (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a (z • b) = z * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n a b := by
  calc
    _ = star (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (z • b) a) := (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_symm n a (z • b)).symm
    _ = star (conj z * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n b a) := by rw [formMetricPair_smul_left]
    _ = _ := by
      rw [star_mul, Complex.star_def, Complex.conj_conj, ← Complex.star_def, Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_symm, mul_comm]

end Model

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) (x : V.analyticSpace)

def projectiveTangentCovectorPair
    (a b : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) : ℂ :=
  let e := chartAt V.analyticModel x
  let he := chart_mem_atlas V.analyticModel x
  let hx := mem_chart_source V.analyticModel x
  let τ := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx
  Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (e x) (e.map_source hx) n
    (a.compContinuousLinearMap τ.symm.toContinuousLinearMap)
    (b.compContinuousLinearMap τ.symm.toContinuousLinearMap)

theorem projectiveFormPointPair_eq_tangentPair
    (a b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x = projectiveTangentCovectorPair V n x (a x) (b x) := by
  have h (c : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
      c.inChart (chartAt V.analyticModel x) (chartAt V.analyticModel x x) =
        (c x).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (chartAt V.analyticModel x)
          (chart_mem_atlas V.analyticModel x) x (mem_chart_source V.analyticModel x)).symm.toContinuousLinearMap := by
    ext v
    exact Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at c _ (chart_mem_atlas V.analyticModel x) x (mem_chart_source V.analyticModel x) v
  dsimp only [Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair, projectiveTangentCovectorPair]
  rw [h a, h b]

theorem projectiveTangentCovectorPair_symm
    (a b : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    conj (projectiveTangentCovectorPair V n x b a) = projectiveTangentCovectorPair V n x a b :=
  Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_symm n _ _

theorem projectiveTangentCovectorPair_nonneg
    (a : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    0 ≤ (projectiveTangentCovectorPair V n x a a).re := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n _

theorem projectiveTangentCovectorPair_definite
    (a : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ)
    (ha : projectiveTangentCovectorPair V n x a a = 0) : a = 0 := by
  let e := chartAt V.analyticModel x
  let he := chart_mem_atlas V.analyticModel x
  let hx := mem_chart_source V.analyticModel x
  let τ := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx
  have hz : a.compContinuousLinearMap τ.symm.toContinuousLinearMap = 0 :=
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair_definite V e he (e x) (e.map_source hx) n _ ha
  ext v
  change a v = 0
  have hv := congrArg (fun b : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel n => b (fun j => τ (v j))) hz
  change a (fun j => τ.symm (τ (v j))) = 0 at hv
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hv

theorem projectiveTangentCovectorPair_self_im_zero
    (a : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    (projectiveTangentCovectorPair V n x a a).im = 0 := by
  have h := congrArg Complex.im (projectiveTangentCovectorPair_symm V n x a a)
  rw [Complex.conj_im] at h
  linarith

theorem projectiveTangentCovectorPair_add_left
    (a b c : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) :
    projectiveTangentCovectorPair V n x (a + b) c =
      projectiveTangentCovectorPair V n x a c + projectiveTangentCovectorPair V n x b c := by
  let e := chartAt V.analyticModel x
  let he := chart_mem_atlas V.analyticModel x
  let hx := mem_chart_source V.analyticModel x
  let τ := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx
  let T := fun d : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ =>
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V e he (e x) (e.map_source hx) n (d.compContinuousLinearMap τ.symm.toContinuousLinearMap)
  have hT : T (a + b) = T a + T b := by
    ext v
    rfl
  change Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (T (a + b)) (T c) = Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (T a) (T c) + Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n (T b) (T c)
  rw [hT, formMetricPair_add_left]

theorem projectiveTangentCovectorPair_smul_left
    (a b : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) (z : ℂ) :
    projectiveTangentCovectorPair V n x (z • a) b = conj z * projectiveTangentCovectorPair V n x a b := by
  dsimp only [projectiveTangentCovectorPair, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair]
  have heq : Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V (chartAt V.analyticModel x) (chart_mem_atlas V.analyticModel x)
      (chartAt V.analyticModel x x) ((chartAt V.analyticModel x).map_source (mem_chart_source V.analyticModel x)) n
      ((z • a).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (chartAt V.analyticModel x)
        (chart_mem_atlas V.analyticModel x) x (mem_chart_source V.analyticModel x)).symm.toContinuousLinearMap) =
    z • Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.metricCoordinateForm V (chartAt V.analyticModel x) (chart_mem_atlas V.analyticModel x)
      (chartAt V.analyticModel x x) ((chartAt V.analyticModel x).map_source (mem_chart_source V.analyticModel x)) n
      (a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv (chartAt V.analyticModel x)
        (chart_mem_atlas V.analyticModel x) x (mem_chart_source V.analyticModel x)).symm.toContinuousLinearMap) := by
    ext v
    rfl
  rw [heq, formMetricPair_smul_left]

theorem projectiveTangentCovectorPair_smul_right
    (a b : TangentSpace 𝓘(ℝ, V.analyticModel) x [⋀^Fin n]→L[ℝ] ℂ) (z : ℂ) :
    projectiveTangentCovectorPair V n x a (z • b) = z * projectiveTangentCovectorPair V n x a b := by
  calc
    _ = conj (projectiveTangentCovectorPair V n x (z • b) a) :=
      (projectiveTangentCovectorPair_symm V n x a (z • b)).symm
    _ = conj (conj z * projectiveTangentCovectorPair V n x b a) := by
      rw [projectiveTangentCovectorPair_smul_left]
    _ = _ := by rw [map_mul, Complex.conj_conj, projectiveTangentCovectorPair_symm]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair
