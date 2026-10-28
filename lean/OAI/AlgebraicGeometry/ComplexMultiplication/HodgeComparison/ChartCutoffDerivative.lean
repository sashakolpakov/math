import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange

/-! # Chart Cutoff Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffDerivative.CM.Construction

noncomputable section

section

/-! The chart cutoff product rule uses the actual global exterior
derivative, and its derivatives remain in the same compact support. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff

theorem varietyScalarChartCutoff_tsupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    tsupport (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f) ⊆ tsupport g :=
  closure_minimal ((SobolevIs.CM.Construction.supportedSchwartzSubmodule_mem_iff _ _).mp
    (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff_support V e he g hgc hg f)) (isClosed_tsupport _)

theorem varietyScalarChartCutoff_derivative_support (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (m : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    tsupport (∂_{m} (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f) : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) ⊆ tsupport g :=
  (SchwartzMap.tsupport_lineDerivOp_subset m _).trans (varietyScalarChartCutoff_tsupport V e he g hgc hg f)

theorem varietyScalarChartCutoff_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (i : ι) :
    (∂_{b i} (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f) : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z =
      (∂_{b i} g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z * ScalarChartLocalization.CM.Construction.varietyScalarChart V e f z +
      g z * GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
        (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) i := by
  have hd := ScalarChartLocalization.CM.Construction.varietyScalarChart_differential V e he b f (e.map_target hz) i
  rw [e.right_inv hz, ContinuousLinearEquiv.symm_apply_apply] at hd
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => g y * ScalarChartLocalization.CM.Construction.varietyScalarChart V e f y) z (b i) = _
  rw [fderiv_fun_mul g.differentiableAt
    (((ScalarChartLocalization.CM.Construction.varietyScalarChart_smooth V e he f).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp))]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [← hd, ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

theorem schwartz_derivative_compact_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport (g : E → ℂ)) (m : E) :
    HasCompactSupport (∂_{m} g : 𝓢(E, ℂ)) :=
  hgc.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset m g)

end

/-! Uniform L2 bounds for the derivatives of actual localized smooth
functions, in terms of their global function and differential L2 norms. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap LineDeriv

theorem varietyScalarChartCutoff_derivative_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (i : ι),
      ‖(∂_{b i} (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f)).toLp 2 volume‖ ≤
        B * (‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ + ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖) := by
  classical
  let K : Set V.analyticSpace := (fun z => e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) '' tsupport g
  have hK : IsCompact K := hgc.image_of_continuousOn
    (e.continuousOn_symm.comp (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous.continuousOn hg)
  have hKe : K ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hg hz)
  obtain ⟨a, ha, hframe⟩ := OneFormFrameChange.CM.Construction.varietyOneFormInChart_global_bound V C b e he hK hKe
  let dg (i : ι) : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) := ∂_{b i} g
  have hdgc (i : ι) : HasCompactSupport (dg i : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) :=
    schwartz_derivative_compact_support g hgc (b i)
  have hdgU (i : ι) : tsupport (dg i) ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    (SchwartzMap.tsupport_lineDerivOp_subset (b i) g).trans hg
  let T (i : ι) : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he (dg i) (hdgc i) (hdgU i)
  let R : Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ]
      Lp (EuclideanSpace ℂ ι) 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg
  let A : ℝ := ∑ i, ‖T i‖
  refine ⟨A + a * ‖R‖, by dsimp [A]; positivity, ?_⟩
  intro f i
  let G := ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f
  let H := ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he (dg i) (hdgc i) (hdgU i) f
  let P : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := (∂_{b i} G).toLp 2 volume
  let Q : Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := H.toLp 2 volume
  let D := GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f
  have hrem : ‖P - Q‖ ≤ a * ‖R D‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub P Q, (∂_{b i} G).coeFn_toLp 2 volume, H.coeFn_toLp 2 volume,
      ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae V e he g hgc hg D
        (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))
        (GlobalLp.CM.Construction.varietyOneFormL2_coe V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))] with z hsub hP hQ hR
    change ‖(P - Q) z‖ ≤ a * ‖R D z‖
    rw [hsub]
    change ‖P z - Q z‖ ≤ _
    rw [hP, hQ, hR]
    by_cases hz : z ∈ tsupport g
    · have hGK := varietyScalarChartCutoff_derivative V e he b g hgc hg f (hg hz) i
      have hH : H z = (∂_{b i} g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z * ScalarChartLocalization.CM.Construction.varietyScalarChart V e f z := rfl
      change ‖(∂_{b i} G : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z - H z‖ ≤ _
      rw [hGK, hH, add_sub_cancel_left]
      rw [norm_mul, norm_smul]
      have hcomp := PiLp.norm_apply_le (GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
        (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) i
      have hfbound := hframe (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) ⟨z, hz, rfl⟩
      calc
        _ ≤ ‖g z‖ * (a * ‖GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
            (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))‖) :=
          mul_le_mul_of_nonneg_left (hcomp.trans hfbound) (norm_nonneg _)
        _ = _ := by ring
    · have hGz : (∂_{b i} G : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz
          (varietyScalarChartCutoff_derivative_support V e he g hgc hg f (b i) h))
      have hdz : dg i z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset (b i) g h))
      have hHz : H z = 0 := by
        change dg i z * ScalarChartLocalization.CM.Construction.varietyScalarChart V e f z = 0
        rw [hdz, zero_mul]
      rw [hGz, hHz, sub_self, norm_zero, image_eq_zero_of_notMem_tsupport hz, zero_smul, norm_zero, mul_zero]
  have hQbound : ‖Q‖ ≤ A * ‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ := by
    have hQeq : Q = T i (GlobalLp.CM.Construction.varietySmoothScalarL2 V f) := (ChartCutoffLp.CM.Construction.varietyChartCutoffL2_smooth V e he (dg i) (hdgc i) (hdgU i) f).symm
    rw [hQeq]
    apply ((T i).le_opNorm _).trans
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => norm_nonneg (T j)) (Finset.mem_univ i)) (norm_nonneg _)
  have hRbound : ‖R D‖ ≤ ‖R‖ * ‖D‖ := R.le_opNorm D
  have htriangle : ‖P‖ ≤ ‖P - Q‖ + ‖Q‖ := by
    simpa only [sub_add_cancel] using norm_add_le (P - Q) Q
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => norm_nonneg (T j))
  change ‖P‖ ≤ (A + a * ‖R‖) * (‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ + ‖D‖)
  nlinarith [mul_nonneg hA (norm_nonneg D), mul_nonneg
    (mul_nonneg ha.le (norm_nonneg R)) (norm_nonneg (GlobalLp.CM.Construction.varietySmoothScalarL2 V f))]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffDerivative.CM.Construction
