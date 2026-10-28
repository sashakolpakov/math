import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction

noncomputable section

section

/-! Positive smooth volume densities of the genuine projective metric. -/

open scoped ContDiff _root_.Manifold
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def bilinearUnderlying (B : E →L[ℝ] E →L[ℝ] ℝ) : LinearMap.BilinForm ℝ E :=
  (ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap

def metricMatrix (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℝ :=
  (bilinearUnderlying B).toMatrix b

theorem metricMatrix_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (i j : ι) :
    metricMatrix b B i j = B (b i) (b j) := by
  rw [metricMatrix, LinearMap.BilinForm.toMatrix_apply]
  rfl

theorem metricMatrix_posDef (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v : E, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    (metricMatrix b B).PosDef := by
  apply ((bilinearUnderlying B).posDef_toQuadraticMap_iff_matrix b ⟨hsym⟩).mp
  exact hpos

theorem metricMatrix_det_pos (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v : E, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    0 < (metricMatrix b B).det :=
  (metricMatrix_posDef b B hsym hpos).det_pos

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem metricMatrix_det_smoothOn (b : Module.Basis ι ℝ E) (B : F → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set F} (hB : ContDiffOn ℝ ∞ B U) :
    ContDiffOn ℝ ∞ (fun x => (metricMatrix b (B x)).det) U := by
  have hcell (i j : ι) : ContDiffOn ℝ ∞ (fun x => B x (b i) (b j)) U :=
    (hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  simp only [Matrix.det_apply', metricMatrix_apply]
  fun_prop

def metricDensity (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  Real.sqrt (metricMatrix b B).det

theorem metricDensity_pos (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v : E, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    0 < metricDensity b B :=
  Real.sqrt_pos.mpr (metricMatrix_det_pos b B hsym hpos)

theorem metricDensity_smoothOn (b : Module.Basis ι ℝ E) (B : F → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set F} (hB : ContDiffOn ℝ ∞ B U)
    (hsym : ∀ x ∈ U, ∀ u v : E, B x u v = B x v u)
    (hpos : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ ∞ (fun x => metricDensity b (B x)) U :=
  (metricMatrix_det_smoothOn b B hB).sqrt
    (fun x hx => (metricMatrix_det_pos b (B x) (hsym x hx) (hpos x hx)).ne')

def varietyMetricDensity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℝ :=
  metricDensity (stdOrthonormalBasis ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)

theorem varietyMetricDensity_pos (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : 0 < varietyMetricDensity V e z :=
  metricDensity_pos _ _ (EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)

theorem varietyMetricDensity_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (varietyMetricDensity V e)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  metricDensity_smoothOn _ _ (EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (fun _ hz => EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz)
    (fun _ hz => EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)

/-- The positive divergence-form coefficient is the inverse metric times
the actual Riemannian volume density. -/
def varietyDirichletCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ :=
  varietyMetricDensity V e z • EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric V e z

theorem varietyDirichletCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    ContDiffOn ℝ ∞ (varietyDirichletCoefficient V e)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  let : IsBoundedSMul ℝ
      (EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
  exact
  ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ)
    (F := EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (varietyMetricDensity_smooth V e he) (EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_smooth V e he)

theorem varietyDirichletCoefficient_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hu : u ≠ 0) :
    0 < varietyDirichletCoefficient V e z u u := by
  change 0 < varietyMetricDensity V e z * EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric V e z u u
  exact mul_pos (varietyMetricDensity_pos V e he hz) (EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_positive V e he hz u hu)

theorem varietyDirichletCoefficient_symmetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    varietyDirichletCoefficient V e z u v = varietyDirichletCoefficient V e z v u := by
  change varietyMetricDensity V e z * EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric V e z u v =
    varietyMetricDensity V e z * EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric V e z v u
  rw [EuclideanMetric.CM.Construction.varietyEuclideanInverseMetric_symmetric V e he hz]

theorem varietyDirichletCoefficient_uniform_lower_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ u : EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      c * ‖u‖ * ‖u‖ ≤ varietyDirichletCoefficient V e z u u :=
  MetricBounds.CM.Construction.positive_bilinear_uniform_lower_bound _ hK
    ((varietyDirichletCoefficient_smooth V e he).continuousOn.mono hKU)
    (fun _ hz => varietyDirichletCoefficient_positive V e he (hKU hz))

theorem varietyDirichletCoefficient_uniform_upper_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ u v : EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      |varietyDirichletCoefficient V e z u v| ≤ C * ‖u‖ * ‖v‖ :=
  MetricBounds.CM.Construction.bilinear_uniform_upper_bound _ hK
    ((varietyDirichletCoefficient_smooth V e he).continuousOn.mono hKU)

end

/-! Extension of the actual real metric energy to complex-valued gradients. -/

open scoped ContDiff

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def complexGradientComponent (b : OrthonormalBasis ι ℝ E) (P : ℂ →L[ℝ] ℝ) :
    EuclideanSpace ℂ ι →L[ℝ] E :=
  ∑ i, ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i)).comp
    (P.comp (((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).toContinuousLinearMap).restrictScalars ℝ))

theorem complexGradientComponent_apply (b : OrthonormalBasis ι ℝ E) (P : ℂ →L[ℝ] ℝ)
    (z : EuclideanSpace ℂ ι) : complexGradientComponent b P z = ∑ i, P (z i) • b i := by
  simp only [complexGradientComponent, sum_apply]
  rfl

theorem complexGradientComponent_inner (b : OrthonormalBasis ι ℝ E) (P Q : ℂ →L[ℝ] ℝ)
    (z w : EuclideanSpace ℂ ι) :
    inner ℝ (complexGradientComponent b P z) (complexGradientComponent b Q w) =
      ∑ i, P (z i) * Q (w i) := by
  rw [complexGradientComponent_apply, complexGradientComponent_apply, b.orthonormal.inner_sum]
  simp only [starRingEnd_apply, star_trivial]

theorem complexGradientComponent_norm_sq (b : OrthonormalBasis ι ℝ E) (z : EuclideanSpace ℂ ι) :
    ‖complexGradientComponent b Complex.reCLM z‖ ^ 2 +
      ‖complexGradientComponent b Complex.imCLM z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    complexGradientComponent_inner, complexGradientComponent_inner,
    ← Finset.sum_add_distrib, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change (z i).re * (z i).re + (z i).im * (z i).im = ‖z i‖ ^ 2
  exact (Complex.normSq_apply (z i)).symm.trans (Complex.normSq_eq_norm_sq _)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback of continuous bilinear forms, as a continuous linear map in the form. -/
def bilinearAlong (L : F →L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ F (E →L[ℝ] ℝ) (F →L[ℝ] ℝ)
    ((ContinuousLinearMap.compL ℝ F E ℝ).flip L)).comp
      ((ContinuousLinearMap.compL ℝ F E (E →L[ℝ] ℝ)).flip L)

theorem bilinearAlong_apply (L : F →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : F) :
    bilinearAlong L B u v = B (L u) (L v) := rfl

def bilinearAlongPair (L R : F →L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) := by
  let : ContinuousAdd (F →L[ℝ] F →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd (F →L[ℝ] F →L[ℝ] ℝ)
      inferInstance inferInstance inferInstance
  exact bilinearAlong L + bilinearAlong R

def complexGradientMetric (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ) :=
  bilinearAlongPair (complexGradientComponent b Complex.reCLM) (complexGradientComponent b Complex.imCLM)

theorem complexGradientMetric_apply (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (z w : EuclideanSpace ℂ ι) :
    complexGradientMetric b B z w =
      B (complexGradientComponent b Complex.reCLM z) (complexGradientComponent b Complex.reCLM w) +
      B (complexGradientComponent b Complex.imCLM z) (complexGradientComponent b Complex.imCLM w) := rfl

theorem complexGradientMetric_lower_bound (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ} (hB : ∀ u : E, c * ‖u‖ * ‖u‖ ≤ B u u)
    (z : EuclideanSpace ℂ ι) : c * ‖z‖ * ‖z‖ ≤ complexGradientMetric b B z z := by
  have hR := hB (complexGradientComponent b Complex.reCLM z)
  have hI := hB (complexGradientComponent b Complex.imCLM z)
  rw [complexGradientMetric_apply]
  have hnorm := complexGradientComponent_norm_sq b z
  calc
    c * ‖z‖ * ‖z‖ = c * (‖complexGradientComponent b Complex.reCLM z‖ ^ 2 +
        ‖complexGradientComponent b Complex.imCLM z‖ ^ 2) := by rw [hnorm]; ring
    _ = c * ‖complexGradientComponent b Complex.reCLM z‖ * ‖complexGradientComponent b Complex.reCLM z‖ +
        c * ‖complexGradientComponent b Complex.imCLM z‖ * ‖complexGradientComponent b Complex.imCLM z‖ := by ring
    _ ≤ _ := add_le_add hR hI

theorem complexGradientMetric_symmetric (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v : E, B u v = B v u)
    (z w : EuclideanSpace ℂ ι) : complexGradientMetric b B z w = complexGradientMetric b B w z := by
  rw [complexGradientMetric_apply, complexGradientMetric_apply, hB, hB _ (complexGradientComponent b Complex.imCLM w)]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction
