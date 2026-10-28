import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp

/-! # One Form Frame Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange.CM.Construction

noncomputable section

/-! The actual component transition law for one-forms in compact chart
frames, including continuity of its operator coefficients on overlaps. -/

open Set
open scoped _root_.Manifold ContDiff

variable {ι : Type*} [Fintype ι]

def varietyCovectorOfFormValue (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ :=
  ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V.analyticModel)
    (F := ℂ) (0 : Fin 1)).symm φ).comp
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ)

theorem varietyOneFormComponents_eq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) :
    GlobalLp.CM.Construction.varietyOneFormComponents V b φ = GlobalLp.CM.Construction.complexCovectorComponents b (varietyCovectorOfFormValue V φ) := rfl

def varietyEuclideanConjugateOperator (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (T : V.analyticModel →L[ℝ] V.analyticModel) : EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V :=
  ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    (T.comp ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ))

theorem varietyCovectorOfFormValue_pullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) (T : V.analyticModel →L[ℝ] V.analyticModel) :
    varietyCovectorOfFormValue V (φ.compContinuousLinearMap T) =
      (varietyCovectorOfFormValue V φ).comp (varietyEuclideanConjugateOperator V T) := by
  apply ContinuousLinearMap.ext
  intro u
  change φ (fun _ => T (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u)) =
    φ (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm
      (T (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u))))
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem varietyOneFormComponents_pullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (φ : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) (T : V.analyticModel →L[ℝ] V.analyticModel) :
    GlobalLp.CM.Construction.varietyOneFormComponents V b (φ.compContinuousLinearMap T) =
      GlobalLp.CM.Construction.complexCovectorPullback b (varietyEuclideanConjugateOperator V T) (GlobalLp.CM.Construction.varietyOneFormComponents V b φ) := by
  rw [varietyOneFormComponents_eq, varietyOneFormComponents_eq,
    GlobalLp.CM.Construction.complexCovectorPullback_components, varietyCovectorOfFormValue_pullback]

def varietyOneFormFrameChange (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (x : V.analyticSpace) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  GlobalLp.CM.Construction.complexCovectorPullback b (varietyEuclideanConjugateOperator V (fderiv ℝ (f ∘ e.symm) (e x)))

theorem varietyOneFormInChart_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {x : V.analyticSpace} (hex : x ∈ e.source) (hfx : x ∈ f.source) :
    GlobalLp.CM.Construction.varietyOneFormInChart V b e form x =
      varietyOneFormFrameChange V b e f x (GlobalLp.CM.Construction.varietyOneFormInChart V b f form x) := by
  have hxf : e.symm (e x) ∈ f.source := by rwa [e.left_inv hex]
  unfold GlobalLp.CM.Construction.varietyOneFormInChart
  rw [form.val.inChart_transition e f he hf (e.map_source hex) hxf, e.left_inv hex]
  exact varietyOneFormComponents_pullback V b _ _

theorem varietyOneFormFrameChange_continuousOn (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace) :
    ContinuousOn (varietyOneFormFrameChange V b e f) (e.source ∩ f.source) := by
  have hconj : Continuous (varietyEuclideanConjugateOperator V) := by
    exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  intro x hx
  have hxf : e.symm (e x) ∈ f.source := by rw [e.left_inv hx.1]; exact hx.2
  have hD := (Analysis.DifferentialForms.Manifold.Charts.contDiffAt_chart_transition e f he hf (e.map_source hx.1) hxf).continuousAt_fderiv (by simp)
  exact (((GlobalLp.CM.Construction.complexCovectorPullback_continuous b).comp hconj).continuousAt.comp
    (hD.comp (e.continuousAt hx.1))).continuousWithinAt

/-- On a compact subset of any chart, its one-form components are bounded
by the components in the chosen global measurable frame, uniformly in the form. -/
theorem varietyOneFormInChart_global_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1),
      ∀ x ∈ K, ‖GlobalLp.CM.Construction.varietyOneFormInChart V b e form x‖ ≤ B * ‖GlobalLp.CM.Construction.varietyOneFormField V C b form x‖ := by
  classical
  have hbound (i : Fin C.size) : ∃ B : ℝ, ∀ x ∈ K ∩ C.compactSet i,
      ‖varietyOneFormFrameChange V b e (C.chart i) x‖ ≤ B :=
    (hK.inter (C.isCompact i)).exists_bound_of_continuousOn
      ((varietyOneFormFrameChange_continuousOn V b e (C.chart i) he (C.chart_mem i)).mono
        (fun x hx => ⟨hKe hx.1, C.subset_source i hx.2⟩))
  choose B hB using hbound
  refine ⟨1 + ∑ i, max (B i) 0, by positivity, ?_⟩
  intro form x hx
  obtain ⟨i, hi⟩ := C.exists_piece x
  have hfield : GlobalLp.CM.Construction.varietyOneFormField V C b form x = GlobalLp.CM.Construction.varietyOneFormInChart V b (C.chart i) form x :=
    C.patchField_eq _ hi
  rw [varietyOneFormInChart_transition V b e (C.chart i) he (C.chart_mem i) form
    (hKe hx) (C.piece_subset_source i hi), hfield]
  apply ((varietyOneFormFrameChange V b e (C.chart i) x).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ B i := hB i x ⟨hx, C.piece_subset i hi⟩
    _ ≤ max (B i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (B j) 0 := Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    _ ≤ _ := by linarith

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange.CM.Construction
