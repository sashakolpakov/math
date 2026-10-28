import OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential
import OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner

/-! # Covector Metric Differential -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovectorMetricDifferential.Constructions

noncomputable section

section

/-! Exact derivative of the induced form metric in its two covector
arguments, holding the tangent metric fixed. -/

open scoped ContDiff

attribute [local instance] BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricDifferential_covectors (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hdet : (BilinearFormMetric.Constructions.bilinearExteriorGram b n B).det ≠ 0)
    (a c da dc : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearMetricDifferential.Constructions.bilinearFormMetricDifferential b n B a c (0, da, dc) =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a dc + BilinearFormMetric.Constructions.bilinearFormMetricPair b n B da c := by
  have ha : HasDerivAt (fun t : ℝ => a + t • da) da 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const da).const_add a using 1
    simp only [one_smul]
  have hc : HasDerivAt (fun t : ℝ => c + t • dc) dc 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const dc).const_add c using 1
    simp only [one_smul]
  let P := fun t : ℝ => (B, a + t • da, c + t • dc)
  have hP : HasDerivAt P (0, da, dc) 0 := (hasDerivAt_const (0 : ℝ) B).prodMk (ha.prodMk hc)
  have hA0 : a + (0 : ℝ) • da = a := by ext v; simp
  have hC0 : c + (0 : ℝ) • dc = c := by ext v; simp
  have hP0 : P 0 = (B, a, c) := by
    change (B, a + (0 : ℝ) • da, c + (0 : ℝ) • dc) = _
    rw [hA0, hC0]
  let F := fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n x.1 x.2.1 x.2.2
  have hF : DifferentiableAt ℝ F (B, a, c) :=
    (BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_joint_contDiffAt b n B a c hdet).differentiableAt (by simp)
  have hchain := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hP hP0.symm
  have hpair := BilinearMetricInner.Constructions.bilinearFormMetricPair_hasDerivAt b n B _ _ da dc 0 ha hc
  have heq := hchain.unique hpair
  change BilinearMetricDifferential.Constructions.bilinearFormMetricDifferential b n B a c (0, da, dc) =
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a + (0 : ℝ) • da) dc +
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B da (c + (0 : ℝ) • dc) at heq
  rw [hA0, hC0] at heq
  exact heq

end

/-! Metric compatibility of the induced connection on actual alternating
covectors, derived by differentiating coordinate invariance of their pairing. -/

open scoped ContDiff

attribute [local instance] BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E D ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_fderiv (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (a c : D → DifferentialForms.Manifold.Basic.FormValue E n) (x u : D)
    (hB : DifferentiableAt ℝ B x) (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hdet : (BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)).det ≠ 0) :
    fderiv ℝ (fun y => BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y)) x u =
      BilinearMetricDifferential.Constructions.bilinearFormMetricDifferential b n (B x) (a x) (c x)
        (fderiv ℝ B x u, fderiv ℝ a x u, fderiv ℝ c x u) := by
  have hF := (BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_joint_contDiffAt b n (B x) (a x) (c x) hdet).differentiableAt (by simp)
  have h := hF.hasFDerivAt.comp x (hB.hasFDerivAt.prodMk (ha.hasFDerivAt.prodMk hc.hasFDerivAt))
  exact congrArg (fun L : D →L[ℝ] ℂ => L u) h.fderiv

theorem bilinearFormMetricDifferential_connection (b : Module.Basis ι ℝ E) (n : ℕ)
    (B T : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (A : E →L[ℝ] E)
    (hT : T = MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback B A) (a c da dc : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearMetricDifferential.Constructions.bilinearFormMetricDifferential b n B a c (T, da, dc) =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (dc - CovectorConnection.Constructions.covectorInfinitesimalAction n A c) +
        BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (da - CovectorConnection.Constructions.covectorInfinitesimalAction n A a) c := by
  have hsplit : (T, da, dc) =
      (MetricPullbackCurve.Constructions.bilinearMetricInfinitesimalPullback B A, CovectorConnection.Constructions.covectorInfinitesimalAction n A a, CovectorConnection.Constructions.covectorInfinitesimalAction n A c) +
        (0, da - CovectorConnection.Constructions.covectorInfinitesimalAction n A a, dc - CovectorConnection.Constructions.covectorInfinitesimalAction n A c) := by
    rw [hT]
    apply Prod.ext
    · exact (add_zero _).symm
    · apply Prod.ext
      · change da = CovectorConnection.Constructions.covectorInfinitesimalAction n A a + (da - CovectorConnection.Constructions.covectorInfinitesimalAction n A a)
        abel
      · change dc = CovectorConnection.Constructions.covectorInfinitesimalAction n A c + (dc - CovectorConnection.Constructions.covectorInfinitesimalAction n A c)
        abel
  rw [hsplit, map_add, BilinearMetricDifferential.Constructions.bilinearFormMetricDifferential_pullback b n B hB hpos, zero_add,
    bilinearFormMetricDifferential_covectors b n B (BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n B hB hpos)]

theorem bilinearFormMetricPair_covariant_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a c : E → DifferentialForms.Manifold.Basic.FormValue E n) (x u : E)
    (hB : DifferentiableAt ℝ B x) (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hBs : ∀ v w, B x v w = B x w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hΓ : ∀ v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w) :
    fderiv ℝ (fun y => BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y)) x u =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (CovectorConnection.Constructions.covectorConnectionDerivative n Γ c x u) +
        BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x u) (c x) := by
  rw [bilinearFormMetricPair_fderiv b n B a c x u hB ha hc (BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) hBs hpos),
    CovectorConnection.Constructions.covectorConnectionDerivative_apply, CovectorConnection.Constructions.covectorConnectionDerivative_apply]
  apply bilinearFormMetricDifferential_connection b n (B x) (fderiv ℝ B x u) hBs hpos (Γ x u)
  ext v w
  exact (hΓ v w).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.CovectorMetricDifferential.Constructions
