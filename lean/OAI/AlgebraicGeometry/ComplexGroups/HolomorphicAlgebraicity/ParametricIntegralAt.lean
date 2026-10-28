import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Parametric Integral At -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral

noncomputable section

/-!
# Holomorphic parameter dependence of contour integrals

Continuous parameter derivatives admit a uniform bound on a compact
parameter ball times the integration interval. This supplies the domination
needed to differentiate under the integral.
-/

open Set Filter _root_.Metric _root_.Complex _root_.MeasureTheory
open scoped _root_.Topology Interval

theorem differentiableAt_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E → ℝ → ℂ} {F' : E → ℝ → E →L[ℂ] ℂ} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ uIcc a b))
    (hF' : ContinuousOn (Function.uncurry F') (U ×ˢ uIcc a b))
    (hd : ∀ y ∈ U, ∀ t ∈ uIcc a b, HasFDerivAt (fun z => F z t) (F' y t) y) :
    DifferentiableAt ℂ (fun y => ∫ t in a..b, F y t) x := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hc : IsCompact (closedBall x r ×ˢ uIcc a b) :=
    (isCompact_closedBall x r).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (hF'.mono (prod_mono hball Subset.rfl))
  have hFc (y : E) (hy : y ∈ U) : ContinuousOn (F y) (uIcc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hy, ht⟩)
  have hF'c : ContinuousOn (F' x) (uIcc a b) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx, ht⟩)
  apply (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (F := F) (F' := F')
    (s := ball x r) (bound := fun _ => C) (ball_mem_nhds x hr) ?_
    (hFc x hx).intervalIntegrable ?_ ?_ intervalIntegrable_const ?_).differentiableAt
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ((hFc y hy).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact (hF'c.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht y hy =>
      hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t ht y hy =>
      hd y (hball (ball_subset_closedBall hy)) t (uIoc_subset_uIcc ht)

theorem differentiableAt_circleIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E → ℂ → ℂ} {F' : E → ℂ → E →L[ℂ] ℂ} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ sphere c R))
    (hF' : ContinuousOn (Function.uncurry F') (U ×ˢ sphere c R))
    (hd : ∀ y ∈ U, ∀ z ∈ sphere c R, HasFDerivAt (fun p => F p z) (F' y z) y) :
    DifferentiableAt ℂ (fun y => ∮ z in C(c, R), F y z) x := by
  let G : E → ℝ → ℂ := fun y t => deriv (circleMap c R) t • F y (circleMap c R t)
  let G' : E → ℝ → E →L[ℂ] ℂ := fun y t =>
    deriv (circleMap c R) t • F' y (circleMap c R t)
  have hmap : Continuous (fun p : E × ℝ => (p.1, circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hmaps : MapsTo (fun p : E × ℝ => (p.1, circleMap c R p.2))
      (U ×ˢ uIcc 0 (2 * Real.pi)) (U ×ˢ sphere c R) :=
    fun p hp => ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  have hder : Continuous (fun p : E × ℝ => deriv (circleMap c R) p.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul_const I
  have hGc : ContinuousOn (Function.uncurry G) (U ×ˢ uIcc 0 (2 * Real.pi)) :=
    hder.continuousOn.smul (hF.comp hmap.continuousOn hmaps)
  have hG'c : ContinuousOn (Function.uncurry G') (U ×ˢ uIcc 0 (2 * Real.pi)) :=
    hder.continuousOn.smul (hF'.comp hmap.continuousOn hmaps)
  have hGd : ∀ y ∈ U, ∀ t ∈ uIcc 0 (2 * Real.pi),
      HasFDerivAt (fun p => G p t) (G' y t) y := by
    intro y hy t _
    exact (hd y hy _ (circleMap_mem_sphere c hR t)).const_smul
      (deriv (circleMap c R) t)
  exact differentiableAt_intervalIntegral hU hx hGc hG'c hGd

/-- A fixed continuous weight on the circle preserves holomorphic parameter
dependence of the integral of a jointly holomorphic function. -/
theorem differentiableAt_weighted_circleIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUW : U ×ˢ sphere c R ⊆ W) {w : ℂ → ℂ} (hw : ContinuousOn w (sphere c R)) :
    DifferentiableAt ℂ (fun y => ∮ z in C(c, R), w z * F (y, z)) x := by
  let D : E → ℂ → E →L[ℂ] ℂ := fun y z =>
    w z • (fderiv ℂ F (y, z)).comp (ContinuousLinearMap.inl ℂ E ℂ)
  have hwc : ContinuousOn (fun p : E × ℂ => w p.2) (U ×ˢ sphere c R) :=
    hw.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hcd := HolomorphicRegularity.Constructions.Regularity.contDiffOn_one_of_differentiableOn_finiteDimensional hW hF
  have hD : ContinuousOn (Function.uncurry D) (U ×ˢ sphere c R) :=
    hwc.smul (((hcd.continuousOn_fderiv_of_isOpen hW le_rfl).mono hUW).clm_comp
      continuousOn_const)
  apply differentiableAt_circleIntegral (F := fun y z => w z * F (y, z)) (F' := D) hU hx hR
    (hwc.fun_mul (hF.continuousOn.mono hUW)) hD
  intro y hy z hz
  exact ((hF.differentiableAt (hW.mem_nhds (hUW ⟨hy, hz⟩))).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left y z)).const_smul (w z)

/-- Applying a holomorphic map's derivative to a fixed direction remains
holomorphic; Cauchy's derivative formula reduces this to a parameter integral. -/
theorem differentiableAt_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) (v : E) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, V, hV, hxV, hball⟩ := HolomorphicRegularity.Constructions.Regularity.exists_disk_neighborhood hU hx v
  let W : Set (E × ℂ) := (fun p => p.1 + p.2 • v) ⁻¹' U
  have hmap : Differentiable ℂ (fun p : E × ℂ => p.1 + p.2 • v) :=
    differentiable_fst.add (differentiable_snd.smul_const v)
  have hW : IsOpen W := hU.preimage hmap.continuous
  have hfw : DifferentiableOn ℂ (fun p : E × ℂ => f (p.1 + p.2 • v)) W :=
    hf.comp hmap.differentiableOn (fun _ hp => hp)
  have hw : ContinuousOn (fun z : ℂ => (z ^ 2)⁻¹) (sphere 0 R) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro z hz
    apply pow_ne_zero
    intro hz0
    change z = 0 at hz0
    have hnorm : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    rw [hz0, norm_zero] at hnorm
    exact hR.ne' hnorm.symm
  have hint := differentiableAt_weighted_circleIntegral hW hfw hV hxV hR.le
    (fun p hp => hball p.1 hp.1 p.2 (sphere_subset_closedBall hp.2)) hw
  have heq : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, R), (z ^ 2)⁻¹ * f (y + z • v)) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact HolomorphicRegularity.Constructions.Regularity.fderiv_apply_eq_circleIntegral hU hf y v hR (hball y hy)
  exact (hint.const_mul _).congr_of_eventuallyEq heq

theorem differentiableOn_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E → ℂ} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U :=
  fun _ hx => (differentiableAt_fderiv_apply hU hf hx v).differentiableWithinAt

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt.Constructions.ParametricIntegral
