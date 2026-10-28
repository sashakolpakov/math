import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicIntegralF
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Holomorphic Contour F -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicContour

/-!
# RiemannProjectivity: holomorphic parameter dependence of contour integrals

The circle integral is written as an actual integral over the compact angle
interval. Joint continuity supplies domination, so its complex derivative
is the contour integral of the parameter derivatives.
-/

open Set _root_.MeasureTheory
open scoped _root_.Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem hasFDerivAt_circleIntegral (F : V → ℂ → W) (D : V → ℂ → V →L[ℂ] W)
    {U : Set V} (hU : IsOpen U) (c : ℂ) (R : ℝ)
    (hF : ContinuousOn (fun p : V × ℂ => F p.1 p.2) (U ×ˢ Metric.sphere c |R|))
    (hD : ContinuousOn (fun p : V × ℂ => D p.1 p.2) (U ×ˢ Metric.sphere c |R|))
    (hder : ∀ x ∈ U, ∀ z ∈ Metric.sphere c |R|,
      HasFDerivAt (fun y => F y z) (D x z) x)
    {x : V} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∮ z in C(c, R), F y z) (∮ z in C(c, R), D x z) x := by
  let K := Icc (0 : ℝ) (2 * Real.pi)
  let μ : Measure K := (volume : Measure ℝ).comap Subtype.val
  let : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap'
    (volume : Measure ℝ) continuous_subtype_val (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  let G : V → K → W := fun y t => deriv (circleMap c R) t.val • F y (circleMap c R t.val)
  let D' : V → K → V →L[ℂ] W :=
    fun y t => deriv (circleMap c R) t.val • D y (circleMap c R t.val)
  have hmap : Continuous (fun p : V × K => (p.1, circleMap c R p.2.val)) := by fun_prop
  have hmaps : MapsTo (fun p : V × K => (p.1, circleMap c R p.2.val))
      (U ×ˢ univ) (U ×ˢ Metric.sphere c |R|) :=
    fun p hp => ⟨hp.1, circleMap_mem_sphere' c R p.2.val⟩
  have hscalar : Continuous (fun p : V × K => deriv (circleMap c R) p.2.val) := by
    simp_rw [deriv_circleMap]
    fun_prop
  have hG : ContinuousOn (fun p : V × K => G p.1 p.2) (U ×ˢ univ) :=
    hscalar.continuousOn.smul (hF.comp hmap.continuousOn hmaps)
  have hD' : ContinuousOn (fun p : V × K => D' p.1 p.2) (U ×ˢ univ) :=
    hscalar.continuousOn.smul (hD.comp hmap.continuousOn hmaps)
  have hdiff : ∀ y ∈ U, ∀ t : K, HasFDerivAt (fun w => G w t) (D' y t) y := by
    intro y hy t
    exact (hder y hy _ (circleMap_mem_sphere' c R t.val)).const_smul _
  have hI := HolomorphicIntegralF.Constructions.HolomorphicIntegral.hasFDerivAt_integral_of_compact μ G D' hU hG hD' hdiff hx
  have hIF : (fun y => ∮ z in C(c, R), F y z) = (fun y => ∫ t, G y t ∂μ) := by
    funext y
    rw [circleIntegral_def_Icc]
    simpa only [G, μ, K] using! (integral_subtype_comap (μ := volume) (s := Icc (0 : ℝ) (2 * Real.pi)) measurableSet_Icc
      (fun t => deriv (circleMap c R) t • F y (circleMap c R t))).symm
  have hID : (∮ z in C(c, R), D x z) = ∫ t, D' x t ∂μ := by
    rw [circleIntegral_def_Icc]
    simpa only [D', μ, K] using! (integral_subtype_comap (μ := volume) (s := Icc (0 : ℝ) (2 * Real.pi)) measurableSet_Icc
      (fun t => deriv (circleMap c R) t • D x (circleMap c R t))).symm
  rw [hIF, hID]
  exact hI

end Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicContour

namespace Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative

/-!
# RiemannProjectivity: holomorphic directional derivatives in finite dimensions

Cauchy's derivative formula expresses each directional derivative as a
contour integral. The proved parameter-integral theorem then gives its
complex differentiability in the base point.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

theorem differentiableAt_directionalDerivative {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U) (v : V) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  let A : V × ℂ → V := fun p => p.1 + p.2 • v
  have hA : Continuous A := continuous_fst.add (continuous_snd.smul continuous_const)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hU.preimage hA) (x, 0)
    (by simpa [A] using hx)
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hmem : ∀ y ∈ closedBall x R, ∀ z ∈ closedBall (0 : ℂ) R, y + z • v ∈ U := by
    intro y hy z hz
    apply hsub (a := (y, z))
    change dist (y, z) (x, 0) < r
    rw [Prod.dist_eq]
    exact max_lt ((mem_closedBall.mp hy).trans_lt (half_lt_self hr))
      ((mem_closedBall.mp hz).trans_lt (half_lt_self hr))
  have hmaps : MapsTo A (ball x R ×ˢ sphere (0 : ℂ) |R|) U := by
    intro p hp
    apply hmem p.1 (ball_subset_closedBall hp.1) p.2
    simpa only [abs_of_pos hR] using sphere_subset_closedBall hp.2
  have hf1 : ContDiffOn ℂ 1 f U := fun y hy =>
    (HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hf hy).contDiffWithinAt
  have hDf : ContinuousOn (fderiv ℂ f) U := hf1.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hweight : ContinuousOn (fun p : V × ℂ => (1 : ℂ) / p.2 ^ 2)
      (ball x R ×ˢ sphere (0 : ℂ) |R|) := by
    simp only [one_div]
    apply (continuous_snd.pow 2).continuousOn.inv₀
    intro p hp
    apply pow_ne_zero
    intro hz
    have h := mem_sphere.mp hp.2
    simp only [hz, dist_self, abs_of_pos hR] at h
    exact hR.ne' h.symm
  let F : V → ℂ → W := fun y z => (1 / z ^ 2 : ℂ) • f (y + z • v)
  let D : V → ℂ → V →L[ℂ] W := fun y z => (1 / z ^ 2 : ℂ) • fderiv ℂ f (y + z • v)
  have hFc : ContinuousOn (fun p : V × ℂ => F p.1 p.2) (ball x R ×ˢ sphere (0 : ℂ) |R|) :=
    hweight.smul (hf.continuousOn.comp hA.continuousOn hmaps)
  have hDc : ContinuousOn (fun p : V × ℂ => D p.1 p.2) (ball x R ×ˢ sphere (0 : ℂ) |R|) :=
    hweight.smul (hDf.comp hA.continuousOn hmaps)
  have hder : ∀ y ∈ ball x R, ∀ z ∈ sphere (0 : ℂ) |R|,
      HasFDerivAt (fun w => F w z) (D y z) y := by
    intro y hy z hz
    have hpoint := hmaps (show (y, z) ∈ ball x R ×ˢ sphere (0 : ℂ) |R| from ⟨hy, hz⟩)
    have h := ((hf _ hpoint).differentiableAt (hU.mem_nhds hpoint)).hasFDerivAt
    simpa only [F, D, ContinuousLinearMap.comp_id] using!
      (h.comp y ((hasFDerivAt_id y).add_const (z • v))).const_smul (1 / z ^ 2 : ℂ)
  have hI := HolomorphicContour.hasFDerivAt_circleIntegral F D isOpen_ball 0 R
    hFc hDc hder (mem_ball_self hR)
  have hcauchy (y : V) (hy : y ∈ ball x R) :
      (∮ z in C(0, R), F y z) = (2 * Real.pi * Complex.I) • fderiv ℂ f y v := by
    have hline : Differentiable ℂ (fun z : ℂ => y + z • v) :=
      (differentiable_id.smul_const v).const_add y
    have hfl : DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (closedBall 0 R) :=
      hf.comp hline.differentiableOn (fun z hz => hmem y (ball_subset_closedBall hy) z hz)
    have hyU : y ∈ U := by
      simpa only [zero_smul, add_zero] using hmem y (ball_subset_closedBall hy) 0 (mem_closedBall_self hR.le)
    simpa only [F, sub_zero, HolomorphicRegularityAt.Constructions.HolomorphicRegularity.deriv_affineLine
      ((hf y hyU).differentiableAt (hU.mem_nhds hyU)) v] using hfl.deriv_eq_smul_circleIntegral hR
  have hconstant : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have heq : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(0, R), F y z)) := by
    filter_upwards [ball_mem_nhds x hR] with y hy
    rw [hcauchy y hy, smul_smul, inv_mul_cancel₀ hconstant, one_smul]
  exact (hI.differentiableAt.const_smul _).congr_of_eventuallyEq heq

/-- Iterating the directional-derivative result gives every finite order
of complex differentiability on the original open domain. -/
theorem contDiffOn_nat_of_differentiableOn {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (n : ℕ) : ContDiffOn ℂ n f U := by
  induction n generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr
    refine ⟨hf, ?_, contDiffOn_clm_apply.mpr (fun v => ?_)⟩
    · intro h
      simp at h
    · exact ih (fun y hy => (differentiableAt_directionalDerivative hU hf hy v).differentiableWithinAt)

/-- Holomorphic maps between finite-dimensional complex spaces are smooth. -/
theorem contDiffOn_infty_of_differentiableOn {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.mpr (contDiffOn_nat_of_differentiableOn hU hf)

/-- The full continuous linear derivative is holomorphic. -/
theorem differentiableOn_fderiv {f : V → W} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fderiv ℂ f) U := by
  have h := (contDiffOn_nat_of_differentiableOn hU hf 2).fderiv_of_isOpen hU
    (m := 1) (by norm_num)
  exact h.differentiableOn (by norm_num)

end Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative

end

end OAI
