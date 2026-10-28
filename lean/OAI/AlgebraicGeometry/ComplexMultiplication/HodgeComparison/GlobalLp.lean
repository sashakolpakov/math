import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactPatchFields
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection

/-! # Global Lp -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp.CM.Construction

noncomputable section

section

/-! The actual scalar functions of smooth zero-forms embed faithfully in
the global metric L2 space. -/

open _root_.MeasureTheory

def varietySmoothScalar (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] C(V.analyticSpace, ℂ) where
  toFun f := ⟨HolomorphicPrimitive.CM.Construction.zeroFormScalar f, Intersection.CM.Construction.zeroFormScalar_continuous f⟩
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl

def varietySmoothScalarL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ]
      Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (ContinuousMap.toLp 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) ℂ).toLinearMap.comp (varietySmoothScalar V)

theorem varietySmoothScalarL2_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietySmoothScalarL2 V f =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V] HolomorphicPrimitive.CM.Construction.zeroFormScalar f :=
  ContinuousMap.coeFn_toLp (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) (varietySmoothScalar V f)

theorem varietySmoothScalarL2_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Injective (varietySmoothScalarL2 V) := by
  intro f g hfg
  have h : varietySmoothScalar V f = varietySmoothScalar V g :=
    ContinuousMap.toLp_injective (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) hfg
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv]
  exact congrArg (fun q : C(V.analyticSpace, ℂ) => q x) h

end

section

/-! Actual one-form components, measured in a finite compact coordinate
refinement, give the global L2 target for the exterior derivative. -/

open _root_.MeasureTheory Set
open scoped ContDiff _root_.Manifold

variable {ι : Type*} [Fintype ι]

def varietyOneFormComponents (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1 →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    (ContinuousLinearMap.pi (fun i =>
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (b i))).comp
        (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V.analyticModel)
          (F := ℂ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem varietyOneFormComponents_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Basic.FormValue V.analyticModel 1) (i : ι) :
    varietyOneFormComponents V b form i = form (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (b i)) := rfl

def varietyOneFormInChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (x : V.analyticSpace) :
    EuclideanSpace ℂ ι := varietyOneFormComponents V b (form.val.inChart e (e x))

theorem varietyOneFormInChart_continuousOn (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    ContinuousOn (varietyOneFormInChart V b e form) e.source := by
  have hform : ContinuousOn (form.val.inChart e) e.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using
      (form.smooth e he).continuousOn
  exact (varietyOneFormComponents V b).continuous.comp_continuousOn
    (hform.comp e.continuousOn e.mapsTo)

def varietyOneFormField (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    V.analyticSpace → EuclideanSpace ℂ ι :=
  C.patchField (fun i => varietyOneFormInChart V b (C.chart i) form)

theorem varietyOneFormField_memLp (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    MemLp (varietyOneFormField V C b form) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  C.patchField_memLp _ (fun i => (varietyOneFormInChart_continuousOn V b (C.chart i)
    (C.chart_mem i) form).mono (C.subset_source i)) 2

theorem varietyOneFormField_add (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form η : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    varietyOneFormField V C b (form + η) = varietyOneFormField V C b form + varietyOneFormField V C b η := by
  have h (i : Fin C.size) (x : V.analyticSpace) :
      varietyOneFormInChart V b (C.chart i) (form + η) x =
        varietyOneFormInChart V b (C.chart i) form x + varietyOneFormInChart V b (C.chart i) η x := by
    change varietyOneFormComponents V b ((form.val + η.val).inChart (C.chart i) (C.chart i x)) = _
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply, map_add]
    rfl
  unfold varietyOneFormField
  simp_rw [show (fun i => varietyOneFormInChart V b (C.chart i) (form + η)) =
    (fun i x => varietyOneFormInChart V b (C.chart i) form x +
      varietyOneFormInChart V b (C.chart i) η x) from funext fun i => funext (h i)]
  exact C.patchField_add _ _

theorem varietyOneFormField_smul (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (a : ℂ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    varietyOneFormField V C b (a • form) = a • varietyOneFormField V C b form := by
  have h (i : Fin C.size) (x : V.analyticSpace) :
      varietyOneFormInChart V b (C.chart i) (a • form) x =
        a • varietyOneFormInChart V b (C.chart i) form x := by
    apply PiLp.ext
    intro j
    rfl
  unfold varietyOneFormField
  rw [show (fun i => varietyOneFormInChart V b (C.chart i) (a • form)) =
    (fun i x => a • varietyOneFormInChart V b (C.chart i) form x) from funext fun i => funext (h i)]
  exact C.patchField_smul a _

def varietyOneFormL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1 →ₗ[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) where
  toFun form := (varietyOneFormField_memLp V C b form).toLp (varietyOneFormField V C b form)
  map_add' form η := by
    apply Lp.ext
    filter_upwards [(varietyOneFormField_memLp V C b (form + η)).coeFn_toLp,
      (varietyOneFormField_memLp V C b form).coeFn_toLp,
      (varietyOneFormField_memLp V C b η).coeFn_toLp,
      Lp.coeFn_add ((varietyOneFormField_memLp V C b form).toLp _)
        ((varietyOneFormField_memLp V C b η).toLp _)] with x hl hform hη hr
    rw [hl, hr]
    simp only [Pi.add_apply, hform, hη]
    exact congrFun (varietyOneFormField_add V C b form η) x
  map_smul' a form := by
    apply Lp.ext
    filter_upwards [(varietyOneFormField_memLp V C b (a • form)).coeFn_toLp,
      (varietyOneFormField_memLp V C b form).coeFn_toLp,
      Lp.coeFn_smul a ((varietyOneFormField_memLp V C b form).toLp _)] with x hl hform hr
    simp only [RingHom.id_apply]
    rw [hl, hr]
    simp only [Pi.smul_apply, hform]
    exact congrFun (varietyOneFormField_smul V C b a form) x

theorem varietyOneFormL2_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    varietyOneFormL2 V C b form =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V] varietyOneFormField V C b form :=
  (varietyOneFormField_memLp V C b form).coeFn_toLp

def varietySmoothDifferentialL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ]
      Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (varietyOneFormL2 V C b).comp Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

end

/-! Real-linear complex covectors are reconstructed exactly from their
components in a real orthonormal basis. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def complexCovectorComponents (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ ℂ (b i)))

theorem complexCovectorComponents_apply (b : OrthonormalBasis ι ℝ E)
    (q : E →L[ℝ] ℂ) (i : ι) : complexCovectorComponents b q i = q (b i) := rfl

def complexCovectorSynthesis (b : OrthonormalBasis ι ℝ E) :
    EuclideanSpace ℂ ι →L[ℝ] (E →L[ℝ] ℂ) :=
  ∑ i, (ContinuousLinearMap.smulRightL ℝ E ℂ (innerSL ℝ (b i))).comp
    ((((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).toContinuousLinearMap)).restrictScalars ℝ)

theorem complexCovectorSynthesis_apply (b : OrthonormalBasis ι ℝ E)
    (z : EuclideanSpace ℂ ι) (u : E) :
    complexCovectorSynthesis b z u = ∑ i, inner ℝ (b i) u • z i := by
  simp only [complexCovectorSynthesis, sum_apply]
  rfl

theorem complexCovectorSynthesis_components (b : OrthonormalBasis ι ℝ E) (q : E →L[ℝ] ℂ) :
    complexCovectorSynthesis b (complexCovectorComponents b q) = q := by
  apply ContinuousLinearMap.ext
  intro u
  rw [complexCovectorSynthesis_apply]
  simp only [complexCovectorComponents_apply, ← map_smul, ← map_sum, b.sum_repr']

theorem complexCovectorComponents_synthesis (b : OrthonormalBasis ι ℝ E) (z : EuclideanSpace ℂ ι) :
    complexCovectorComponents b (complexCovectorSynthesis b z) = z := by
  classical
  apply PiLp.ext
  intro j
  rw [complexCovectorComponents_apply, complexCovectorSynthesis_apply]
  simp only [b.inner_eq_ite, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem complexCovectorComponents_injective (b : OrthonormalBasis ι ℝ E) :
    Function.Injective (complexCovectorComponents b) :=
  Function.LeftInverse.injective (complexCovectorSynthesis_components b)

def complexCovectorPullback (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  (complexCovectorComponents b).comp
    (((ContinuousLinearMap.compL ℝ E E ℂ).flip T).comp (complexCovectorSynthesis b))

theorem complexCovectorPullback_components (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E) (q : E →L[ℝ] ℂ) :
    complexCovectorPullback b T (complexCovectorComponents b q) =
      complexCovectorComponents b (q.comp T) := by
  change complexCovectorComponents b ((complexCovectorSynthesis b (complexCovectorComponents b q)).comp T) = _
  rw [complexCovectorSynthesis_components]

theorem complexCovectorPullback_continuous (b : OrthonormalBasis ι ℝ E) :
    Continuous (complexCovectorPullback b) := by
  apply Continuous.clm_comp continuous_const
  apply Continuous.clm_comp _ continuous_const
  exact (ContinuousLinearMap.compL ℝ E E ℂ).flip.continuous

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp.CM.Construction
