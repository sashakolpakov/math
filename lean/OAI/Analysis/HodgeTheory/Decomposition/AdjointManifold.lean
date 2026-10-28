import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm
import OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.LocalMetric
import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral
import OAI.Analysis.DifferentialForms.Manifold.SupportedExtension
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition

/-! # Adjoint Manifold -/

namespace OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions

noncomputable section

section

/-! The local formal adjoint satisfies the actual global metric-volume
integration identity for every smooth form supported inside its chart. -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

/-- Integration by parts now pairs genuine manifold forms and uses the global volume. -/
theorem projectiveChartAdjoint_integral
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (ha : ∀ x, x ∉ K → a x = 0) :
    (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x).re
      ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
    ∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a.val x).re
      ∂ MeasureVolume.Constructions.projectiveMetricVolume V := by
  let u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val
  let v := EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) b.val
  let D := LocalAdjoint.Constructions.firstOrderCoordinateOperator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n)
  let M := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e
  let A := AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n v
  have hu : ContDiff ℝ ∞ u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n a hK hKe ha
  have hv : ContDiffOn ℝ ∞ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) b
  have huc : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n a.val hK hKe ha
  have hus : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e n a.val hK hKe ha
  have hleftzero (x : V.analyticSpace) (hx : x ∉ e.source) :
      (ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x).re = 0 := by
    rw [LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V (n + 1) b.val (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x
      (SupportedCoordinates.Constructions.manifold_d_zero_off_closed V n a hK.isClosed ha (fun h => hx (hKe h)))]
    rfl
  have hrightzero (x : V.analyticSpace) (hx : x ∉ e.source) :
      (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a.val x).re = 0 := by
    rw [LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n _ a.val x (ha x (fun h => hx (hKe h)))]
    rfl
  have hrightcont := LocalMetric.Constructions.projectiveFormPointPair_continuous_supported V n
    (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a hK.isClosed e.open_source hKe
      (LocalAdjointForm.Constructions.projectiveChartAdjoint_smooth V e he n b) ha
  have hleftchart := ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x).re)
    ((Complex.continuous_re.comp
      (MetricCoefficients.Constructions.projectiveFormPointPair_continuous V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))).aestronglyMeasurable)
    hleftzero
  have hrightchart := ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (fun x => (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a.val x).re)
    (Complex.continuous_re.comp hrightcont).aestronglyMeasurable hrightzero
  have hDzero (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∉ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : D u z = 0 := by
    have hnot : z ∉ tsupport u := fun h => hz (hus h)
    dsimp only [D, LocalAdjoint.Constructions.firstOrderCoordinateOperator]
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    simp only [zero_apply, map_zero, Finset.sum_const_zero]
  calc
    _ = ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, inner ℝ (M (n + 1) z (v z)) (D u z) := by
      rw [hleftchart]
      apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul, ← EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he (n + 1)
        b.val (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val z hz, SupportedCoordinates.Constructions.supportedEuclideanCoefficients_d V e he n a z hz]
    _ = ∫ z, inner ℝ (M (n + 1) z (v z)) (D u z) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hDzero z hz, inner_zero_right])
    _ = ∫ z, inner ℝ (M n z (A z)) (u z) :=
      LocalAdjointForm.Constructions.projectiveLocalAdjointCoefficients_integration V e he n u v hu hv huc hus
    _ = ∫ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, inner ℝ (M n z (A z)) (u z) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero : u z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hus h))
      rw [hzero, inner_zero_right]
    _ = _ := by
      rw [hrightchart]
      apply setIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      dsimp only
      rw [smul_eq_mul, ← EuclideanForms.Constructions.euclideanChartCoefficients_weighted_inner V e he n
        (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a.val z hz, LocalAdjointForm.Constructions.projectiveChartAdjoint_coefficients V e he n b z hz]
      rw [show u z = EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z from SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val hz]

end

section

/-! Supported weighted local adjoints as global smooth forms. -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)

theorem projectiveFormPointPair_smul_right
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (z : ℂ) (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a (z • b) x = z * ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x := by
  rw [← ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm, Form.Constructions.projectiveFormPointPair_smul_left,
    star_mul, star_star, ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm]
  exact mul_comm _ _

theorem projectiveFormPointPair_smulFunction_move
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (f : V.analyticSpace → ℂ) (x : V.analyticSpace) :
    ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f b) x =
      ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (fun y => star (f y)) a) b x := by
  have hl := LocalMetric.Constructions.projectiveFormPointPair_congr_at V n a (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f b)
    a (f x • b) x rfl rfl
  have hr := LocalMetric.Constructions.projectiveFormPointPair_congr_at V n
    (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (fun y => star (f y)) a) b (star (f x) • a) b x rfl rfl
  rw [hl, hr, projectiveFormPointPair_smul_right, Form.Constructions.projectiveFormPointPair_smul_left, star_star]

theorem conjugateFunction_tsupport (f : V.analyticSpace → ℂ) :
    tsupport (fun x => star (f x)) = tsupport f := by
  apply congrArg closure
  ext x
  simp only [Function.mem_support, star_ne_zero]

theorem conjugateFunction_smooth (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (fun x => star (f x)) :=
  Complex.conjCLE.contDiff.contMDiff.comp hf

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

/-- Multiplying the local adjoint by a subordinate conjugate cutoff yields a global smooth form. -/
def weightedProjectiveChartAdjoint (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) (hs : tsupport f ⊆ e.source)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ofSmooth
    (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (fun x => star (f x)) (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b))
    ((LocalAdjointForm.Constructions.projectiveChartAdjoint_smooth V e he n b).smulFunction_of_tsupport_subset e.open_source
      (conjugateFunction_smooth V f hf).contMDiffOn
      (by rw [conjugateFunction_tsupport]; exact hs))

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

/-- The supported local formula gives the global L² pairing for a scalar-localized test form. -/
theorem weightedProjectiveChartAdjoint_pair
    (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) (hs : tsupport f ⊆ e.source)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    (Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a))).re =
      (Form.Constructions.projectiveL2Pair V n (weightedProjectiveChartAdjoint V n e he f hf hs b) a).re := by
  have h := projectiveChartAdjoint_integral V e he n
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a) b (isClosed_tsupport f).isCompact hs (by
      intro x hx
      rw [DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction_apply, image_eq_zero_of_notMem_tsupport hx]
      exact zero_smul ℂ (a x))
  change RCLike.re (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)).val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V) =
      RCLike.re (∫ x, ProjectiveFormMetric.Constructions.projectiveFormPointPair V n
        (weightedProjectiveChartAdjoint V n e he f hf hs b).val a.val x ∂ MeasureVolume.Constructions.projectiveMetricVolume V)
  rw [← integral_re (Form.Constructions.projectiveFormPointPair_integrable V (n + 1) b _),
    ← integral_re (Form.Constructions.projectiveFormPointPair_integrable V n _ a)]
  change (∫ x, (ProjectiveFormMetric.Constructions.projectiveFormPointPair V (n + 1) b.val
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)).val x).re
      ∂ MeasureVolume.Constructions.projectiveMetricVolume V) = _
  rw [h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact congrArg Complex.re (projectiveFormPointPair_smulFunction_move V n
    (LocalAdjointForm.Constructions.projectiveChartAdjoint V e n b) a.val f x)

end

/-! A global formal adjoint on genuine smooth forms, constructed from the
proved local formulas and a finite smooth partition of unity. -/

open scoped ContDiff _root_.Manifold BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem exists_projective_adjoint_partition :
    ∃ f : MeasureVolume.Constructions.ProjectiveChartIndex V → V.analyticSpace → ℂ,
      (∀ i, ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (f i)) ∧
      (∀ i, tsupport (f i) ⊆ (MeasureVolume.Constructions.projectiveCoverChart V i).source) ∧
      (∀ x, ∑ i, f i x = 1) :=
  DifferentialForms.Manifold.FinitePartition.exists_finite_complex_partition (fun i => (MeasureVolume.Constructions.projectiveCoverChart V i).source)
    (fun i => (MeasureVolume.Constructions.projectiveCoverChart V i).open_source) (MeasureVolume.Constructions.projectiveCoverChart_covers V)

def projectiveAdjointPartition : MeasureVolume.Constructions.ProjectiveChartIndex V → V.analyticSpace → ℂ :=
  (exists_projective_adjoint_partition V).choose

theorem projectiveAdjointPartition_smooth (i : MeasureVolume.Constructions.ProjectiveChartIndex V) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (projectiveAdjointPartition V i) :=
  (exists_projective_adjoint_partition V).choose_spec.1 i

theorem projectiveAdjointPartition_support (i : MeasureVolume.Constructions.ProjectiveChartIndex V) :
    tsupport (projectiveAdjointPartition V i) ⊆ (MeasureVolume.Constructions.projectiveCoverChart V i).source :=
  (exists_projective_adjoint_partition V).choose_spec.2.1 i

theorem projectiveAdjointPartition_sum (x : V.analyticSpace) :
    ∑ i, projectiveAdjointPartition V i x = 1 :=
  (exists_projective_adjoint_partition V).choose_spec.2.2 x

variable (n : ℕ)

theorem projective_partition_forms_sum
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    (∑ i, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (projectiveAdjointPartition V i)
      (projectiveAdjointPartition_smooth V i) a) = a := by
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.eval x (∑ i, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction
    (projectiveAdjointPartition V i) (projectiveAdjointPartition_smooth V i) a) = a x
  rw [map_sum]
  simp only [DifferentialForms.Manifold.Algebra.SmoothManifoldForm.eval_apply, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction_apply]
  rw [← Finset.sum_smul, projectiveAdjointPartition_sum, one_smul]

/-- The global adjoint is a finite sum of actual supported smooth local adjoints. -/
def projectiveGlobalAdjoint
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  ∑ i, weightedProjectiveChartAdjoint V n (MeasureVolume.Constructions.projectiveCoverChart V i)
    (MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i) (projectiveAdjointPartition V i)
    (projectiveAdjointPartition_smooth V i) (projectiveAdjointPartition_support V i) b

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveL2Pair_sum_left {ι : Type*} (s : Finset ι)
    (a : ι → DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Form.Constructions.projectiveL2Pair V n (∑ i ∈ s, a i) b = ∑ i ∈ s, Form.Constructions.projectiveL2Pair V n (a i) b := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_sum, sum_inner]
  simp only [Form.Constructions.smoothToProjectiveL2_inner]

theorem projectiveL2Pair_sum_right {ι : Type*} (s : Finset ι)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : ι → DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Form.Constructions.projectiveL2Pair V n a (∑ i ∈ s, b i) = ∑ i ∈ s, Form.Constructions.projectiveL2Pair V n a (b i) := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_sum, inner_sum]
  simp only [Form.Constructions.smoothToProjectiveL2_inner]

theorem projectiveL2Pair_smul_right
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (z : ℂ) :
    Form.Constructions.projectiveL2Pair V n a (z • b) = z * Form.Constructions.projectiveL2Pair V n a b := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_smul, inner_smul_right, Form.Constructions.smoothToProjectiveL2_inner]

/-- The global real formal-adjoint identity holds for every pair of smooth forms. -/
theorem projectiveGlobalAdjoint_real_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    (Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).re =
      (Form.Constructions.projectiveL2Pair V n (projectiveGlobalAdjoint V n b) a).re := by
  let localA (i : MeasureVolume.Constructions.ProjectiveChartIndex V) := DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction
    (projectiveAdjointPartition V i) (projectiveAdjointPartition_smooth V i) a
  have hsum : (∑ i, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (localA i)) = DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a := by
    rw [← map_sum, projective_partition_forms_sum]
  calc
    _ = (Form.Constructions.projectiveL2Pair V (n + 1) b (∑ i, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (localA i))).re := by rw [hsum]
    _ = ∑ i, (Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (localA i))).re := by
      rw [projectiveL2Pair_sum_right]
      exact map_sum Complex.reCLM _ _
    _ = ∑ i, (Form.Constructions.projectiveL2Pair V n
        (weightedProjectiveChartAdjoint V n (MeasureVolume.Constructions.projectiveCoverChart V i)
          (MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i) (projectiveAdjointPartition V i)
          (projectiveAdjointPartition_smooth V i) (projectiveAdjointPartition_support V i) b) a).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact weightedProjectiveChartAdjoint_pair V n (MeasureVolume.Constructions.projectiveCoverChart V i)
        (MeasureVolume.Constructions.projectiveCoverChart_mem_atlas V i) (projectiveAdjointPartition V i)
        (projectiveAdjointPartition_smooth V i) (projectiveAdjointPartition_support V i) a b
    _ = _ := by
      unfold projectiveGlobalAdjoint
      rw [projectiveL2Pair_sum_left]
      exact (map_sum Complex.reCLM _ _).symm

/-- The genuine global complex L² formal-adjoint identity. -/
theorem projectiveGlobalAdjoint_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) =
      Form.Constructions.projectiveL2Pair V n (projectiveGlobalAdjoint V n b) a := by
  apply Complex.ext
  · exact projectiveGlobalAdjoint_real_pair V n a b
  · have h := projectiveGlobalAdjoint_real_pair V n (Complex.I • a) b
    rw [map_smul, projectiveL2Pair_smul_right, projectiveL2Pair_smul_right] at h
    simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_inj] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions
