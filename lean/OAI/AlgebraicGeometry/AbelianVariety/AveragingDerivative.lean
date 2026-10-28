import OAI.AlgebraicGeometry.AbelianVariety.Averaging
import OAI.AlgebraicGeometry.AbelianVariety.CompactIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Averaging Derivative -/

namespace OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology

noncomputable section

/-!
# Averaging and the de Rham differential for ExteriorCohomology

The invariant-coefficient average is the pointwise integral of translated forms.
Joint chart smoothness and compact integral differentiation show that averaging
commutes with the exterior derivative. Thus an invariant exact form on a compact
commutative Lie group must be zero.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter _root_.MeasureTheory

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}

def translatedValue (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g x : G) :
    E [⋀^Fin n]→L[ℝ] ℂ :=
  ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback (fun h : G => g * h)) x

theorem leftCoefficient_comp_inverse (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g x : G) :
    (Averaging.Constructions.ExteriorCohomology.leftCoefficient form g).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => x⁻¹ * h) x) =
        translatedValue form (g * x⁻¹) x := by
  have he : (fun h : G => g * h) ∘ (fun h : G => x⁻¹ * h) =
      (fun h : G => (g * x⁻¹) * h) := by funext h; exact (mul_assoc g x⁻¹ h).symm
  have hp := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback_comp (fun h : G => x⁻¹ * h)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp))
    (fun h : G => g * h)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp))
  rw [he] at hp
  have hv := congrFun hp.symm x
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_apply, inv_mul_cancel] at hv
  exact hv

theorem translatedValue_eq_coefficient (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (g x : G) :
    translatedValue form g x =
      (Averaging.Constructions.ExteriorCohomology.leftCoefficient form (g * x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => x⁻¹ * h) x) := by
  have h := leftCoefficient_comp_inverse form (g * x) x
  rw [mul_inv_cancel_right] at h
  exact h.symm

theorem translatedValue_continuous (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (x : G) :
    Continuous (fun g => translatedValue form g x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  let T : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => x⁻¹ * h) x
  let L : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM T
  have hc := (Averaging.Constructions.ExteriorCohomology.leftCoefficient_contMDiff form).continuous.comp (continuous_mul_const x)
  exact (L.continuous.comp hc).congr (fun g => (translatedValue_eq_coefficient form g x).symm)

def translatedInChart (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c : OpenPartialHomeomorph G E) (g : G) (y : E) : E [⋀^Fin n]→L[ℝ] ℂ :=
  ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback (fun h : G => g * h)).inChart c y

theorem translatedInChart_continuous (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c : OpenPartialHomeomorph G E) (y : E) :
    Continuous (fun g => translatedInChart form c g y) := by
  let T : E →L[ℝ] E := Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c y
  let L : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM T
  exact L.continuous.comp (translatedValue_continuous form (c.symm y))

theorem translatedInChart_joint_contDiffAt (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c e : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) (he : e ∈ atlas E G)
    {y z : E} (hy : y ∈ c.target) (hz : z ∈ e.target) :
    ContDiffAt ℝ ∞ (fun p : E × E => translatedInChart form c (e.symm p.2) p.1) (y, z) := by
  let d := chartAt E (e.symm z * c.symm y)
  have hd : d ∈ atlas E G := chart_mem_atlas E _
  have htarget : e.symm z * c.symm y ∈ d.source := mem_chart_source E _
  have hcinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
  have heinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hz
  have hm : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
      (fun p : E × E => e.symm p.2 * c.symm p.1) (y, z) :=
    (heinv.comp (y, z) contDiffAt_snd.contMDiffAt).mul
      (hcinv.comp (y, z) contDiffAt_fst.contMDiffAt)
  have hd' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d (e.symm z * c.symm y) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) htarget
  have ht : ContDiffAt ℝ ∞
      (fun p : E × E => d (e.symm p.2 * c.symm p.1)) (y, z) :=
    (hd'.comp (y, z) hm).contDiffAt
  have ht3 : ContDiffAt ℝ ∞
      (fun p : (E × E) × E => d (e.symm p.1.2 * c.symm p.2)) ((y, z), y) := by
    have hp : ContDiffAt ℝ ∞ (fun p : (E × E) × E => (p.2, p.1.2)) ((y, z), y) :=
      contDiffAt_snd.prodMk contDiffAt_fst.snd
    exact ht.comp (f := fun p : (E × E) × E => (p.2, p.1.2)) ((y, z), y) hp
  have hder : ContDiffAt ℝ ∞
      (fun p : E × E => fderiv ℝ (fun w => d (e.symm p.2 * c.symm w)) p.1) (y, z) :=
    ht3.fderiv contDiffAt_fst (by simp)
  have hform := (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.smooth d hd
    (d.map_source htarget)).comp (y, z) ht
  have hs := Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap hform hder
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.preimage_mem_nhds (c.open_target.mem_nhds hy),
    hm.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds htarget)] with p hp hdp
  have hpb := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback_inChart
    (fun h : G => e.symm p.2 * h) c d hc hd hp hdp
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  exact hpb

theorem translatedInChart_fderiv_continuousAt (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) {y : E} (hy : y ∈ c.target)
    (g : G) :
    ContinuousAt (fun p : E × G => fderiv ℝ (translatedInChart form c p.2) p.1) (y, g) := by
  let e := chartAt E g
  have he : e ∈ atlas E G := chart_mem_atlas E g
  have hg : g ∈ e.source := mem_chart_source E g
  have ht := translatedInChart_joint_contDiffAt form c e hc he hy (e.map_source hg)
  have ht3 : ContDiffAt ℝ ∞
      (fun p : (E × E) × E => translatedInChart form c (e.symm p.1.2) p.2)
        ((y, e g), y) := by
    have hp : ContDiffAt ℝ ∞ (fun p : (E × E) × E => (p.2, p.1.2)) ((y, e g), y) :=
      contDiffAt_snd.prodMk contDiffAt_fst.snd
    exact ht.comp ((y, e g), y) hp
  have hder : ContDiffAt ℝ ∞
      (fun p : E × E => fderiv ℝ (translatedInChart form c (e.symm p.2)) p.1) (y, e g) :=
    ht3.fderiv contDiffAt_fst (by simp)
  have hcoord : ContinuousAt (fun p : E × G => (p.1, e p.2)) (y, g) :=
    continuousAt_fst.prodMk ((e.continuousAt hg).comp continuousAt_snd)
  apply (hder.continuousAt.comp (x := (y, g))
    (f := fun p : E × G => (p.1, e p.2)) hcoord).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_source.mem_nhds hg)] with p hp
  change fderiv ℝ (translatedInChart form c p.2) p.1 =
    fderiv ℝ (translatedInChart form c (e.symm (e p.2))) p.1
  rw [e.left_inv hp]

theorem translatedInChart_hasFDerivAt (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (c : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) {y : E} (hy : y ∈ c.target)
    (g : G) :
    HasFDerivAt (translatedInChart form c g)
      (fderiv ℝ (translatedInChart form c g) y) y := by
  exact (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart
    ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).pullback_smooth form.smooth (fun x : G => g * x)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞))) c hc hy).differentiableAt (by simp)
    |>.hasFDerivAt

variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsFiniteMeasure μ]

theorem averageForms_eq_integral_pullback [Measure.IsMulRightInvariant μ]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (x : G) :
    (Averaging.Constructions.ExteriorCohomology.averageForms μ form) x = ∫ g, translatedValue form g x ∂μ := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ, E)) (n := ∞)
  let T : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => x⁻¹ * h) x
  let L : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM T
  change L (∫ g, Averaging.Constructions.ExteriorCohomology.leftCoefficient form g ∂μ) = _
  rw [← L.integral_comp_comm (Averaging.Constructions.ExteriorCohomology.leftCoefficient_integrable μ form)]
  change (∫ g, (Averaging.Constructions.ExteriorCohomology.leftCoefficient form g).compContinuousLinearMap T ∂μ) = _
  calc
    _ = ∫ g, translatedValue form (g * x⁻¹) x ∂μ :=
      integral_congr_ae (ae_of_all _ (fun g => leftCoefficient_comp_inverse form g x))
    _ = _ := integral_mul_right_eq_self (μ := μ) (fun g => translatedValue form g x) x⁻¹

theorem averageForms_inChart_eq_integral [Measure.IsMulRightInvariant μ]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (c : OpenPartialHomeomorph G E) (y : E) :
    (Averaging.Constructions.ExteriorCohomology.averageForms μ form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).inChart c y =
      ∫ g, translatedInChart form c g y ∂μ := by
  let T : E →L[ℝ] E := Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap c y
  let L : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM T
  change L ((Averaging.Constructions.ExteriorCohomology.averageForms μ form) (c.symm y)) =
    ∫ g, L (translatedValue form g (c.symm y)) ∂μ
  rw [averageForms_eq_integral_pullback]
  exact (L.integral_comp_comm
    ((translatedValue_continuous form (c.symm y)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

theorem averageForms_inChart_hasFDerivAt [Measure.IsMulRightInvariant μ]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (c : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G)
    {y : E} (hy : y ∈ c.target) :
    HasFDerivAt ((Averaging.Constructions.ExteriorCohomology.averageForms μ form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n).inChart c)
      (∫ g, fderiv ℝ (translatedInChart form c g) y ∂μ) y := by
  have hi := CompactIntegral.Constructions.ExteriorCohomology.hasFDerivAt_integral_compact (μ := μ) c.open_target hy
    (F := fun y g => translatedInChart form c g y)
    (F' := fun y g => fderiv ℝ (translatedInChart form c g) y)
    (fun z _ => translatedInChart_continuous form c z)
    (fun z hz g => translatedInChart_fderiv_continuousAt form c hc hz g)
    (fun z hz g => translatedInChart_hasFDerivAt form c hc hz g)
  exact hi.congr_of_eventuallyEq
    (Eventually.of_forall (fun z => averageForms_inChart_eq_integral μ form c z))

theorem d_averageForms [Measure.IsMulRightInvariant μ]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Averaging.Constructions.ExteriorCohomology.averageForms μ form) = Averaging.Constructions.ExteriorCohomology.averageForms μ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let c := chartAt E x
  have hc : c ∈ atlas E G := chart_mem_atlas E x
  have hx : x ∈ c.source := mem_chart_source E x
  have hy : c x ∈ c.target := c.map_source hx
  have hchart : (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Averaging.Constructions.ExteriorCohomology.averageForms μ form) :
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G (n + 1)).inChart c (c x) =
      (Averaging.Constructions.ExteriorCohomology.averageForms μ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G (n + 1)).inChart c (c x) := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ c hc hy, averageForms_inChart_eq_integral]
    rw [extDeriv, (averageForms_inChart_hasFDerivAt μ form c hc hy).fderiv]
    let L : (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) →L[ℝ] (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :=
      ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := n) ℝ E ℂ
    let : ContinuousENorm (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) :=
      @SeminormedAddGroup.toContinuousENorm (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) inferInstance
    have hcont : Continuous (fun g => fderiv ℝ (translatedInChart form c g) (c x)) := by
      rw [continuous_iff_continuousAt]
      intro g
      exact (translatedInChart_fderiv_continuousAt form c hc hy g).comp
        (f := fun h : G => (c x, h)) (continuousAt_const.prodMk continuousAt_id)
    change L (∫ g, fderiv ℝ (translatedInChart form c g) (c x) ∂μ) = _
    have hint : Integrable (fun g => fderiv ℝ (translatedInChart form c g) (c x)) μ := by
      exact Continuous.integrable_of_hasCompactSupport
        (E := E →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) hcont (HasCompactSupport.of_compactSpace _)
    have hi := ContinuousLinearMap.integral_comp_comm (μ := μ) (𝕜 := ℝ)
      (E := E →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) (Fₗ := E [⋀^Fin (n + 1)]→L[ℝ] ℂ) L hint
    refine hi.symm.trans ?_
    apply integral_congr_ae
    apply ae_of_all
    intro g
    have hd := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) c hc hy
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback] at hd
    exact hd.symm
  have hcov := congrArg (fun α : E [⋀^Fin (n + 1)]→L[ℝ] ℂ =>
    α.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap c x)) hchart
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ c hc hx,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ c hc hx] at hcov
  exact hcov

theorem averageForms_d_eq_zero [Measure.IsMulRightInvariant μ] [IsMulCommutative G]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    Averaging.Constructions.ExteriorCohomology.averageForms μ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) = 0 := by
  rw [← d_averageForms, Averaging.Constructions.ExteriorCohomology.averageForms_closed]

theorem invariant_exact_eq_zero [Measure.IsMulRightInvariant μ] [IsProbabilityMeasure μ]
    [IsMulCommutative G] (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G (n + 1))
    (hf : form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) (n + 1))
    (other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) (he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d other = form) :
    form = 0 := by
  rw [← Averaging.Constructions.ExteriorCohomology.averageForms_of_invariant μ form hf, ← he, averageForms_d_eq_zero]

end

end OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative.Constructions.ExteriorCohomology
