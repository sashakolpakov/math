import OAI.LieTheory.Semisimple.Integration
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Regularity -/

namespace OAI.LieTheory.Semisimple.Regularity.Constructions.CharacterTriviality

noncomputable section

/-! Automatic smoothness of circle-valued characters, by compact smoothing. -/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology Pointwise

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (𝓘(ℝ, E)) ∞ G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

omit [SecondCountableTopology G] [IsTopologicalGroup G] in
theorem exists_bump_character_integral_ne_zero (χ : G →ₜ* Circle) :
    ∃ b : SmoothBumpFunction (𝓘(ℝ, E)) (1 : G),
      (∫ y, (b y : ℂ) * (χ y : ℂ) ∂μ) ≠ 0 := by
  have hc : Continuous (fun y : G => (χ y : ℂ)) := continuous_subtype_val.comp χ.continuous
  have hn : {y : G | 0 < (χ y : ℂ).re} ∈ 𝓝 1 := by
    apply (isOpen_lt continuous_const (Complex.continuous_re.comp hc)).mem_nhds
    simp
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (1 : G)).mem_iff.mp hn
  refine ⟨b, ?_⟩
  have hint : Integrable (fun y : G => (b y : ℂ) * (χ y : ℂ)) μ :=
    ((Complex.continuous_ofReal.comp b.continuous).mul hc).integrable_of_hasCompactSupport
      ((b.hasCompactSupport.comp_left rfl).mul_right)
  have hpos : 0 < ∫ y, b y * (χ y : ℂ).re ∂μ := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : G))
      (b.continuous.mul (Complex.continuous_re.comp hc))
    · exact (b.continuous.mul (Complex.continuous_re.comp hc)).integrable_of_hasCompactSupport
        b.hasCompactSupport.mul_right
    · intro y
      by_cases hy : b y = 0
      · simp [hy]
      · exact mul_nonneg b.nonneg (le_of_lt (hb (subset_tsupport b hy)))
    · simp
  have hreal : (∫ y, (b y : ℂ) * (χ y : ℂ) ∂μ).re = ∫ y, b y * (χ y : ℂ).re ∂μ := by
    have h := (Complex.reCLM.integral_comp_comm hint).symm
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  intro hz
  rw [← hreal, hz, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

variable [μ.IsMulLeftInvariant]

omit [T2Space G] [SecondCountableTopology G] [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] in
theorem character_smoothing_identity (χ : G →ₜ* Circle)
    (b : G → ℝ) (x : G) :
    (∫ y, (χ y : ℂ) * (b (x⁻¹ * y) : ℂ) ∂μ) =
      (χ x : ℂ) * ∫ y, (b y : ℂ) * (χ y : ℂ) ∂μ := by
  rw [← integral_mul_left_eq_self (fun y => (χ y : ℂ) * (b (x⁻¹ * y) : ℂ)) x]
  simp only [inv_mul_cancel_left, map_mul, Circle.coe_mul]
  simp_rw [mul_assoc, mul_comm (χ _ : ℂ) (b _ : ℂ)]
  exact integral_const_mul _ _

include μ in
theorem contMDiffAt_character_one (χ : G →ₜ* Circle) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (fun y => (χ y : ℂ)) (1 : G) := by
  obtain ⟨b, hb⟩ := exists_bump_character_integral_ne_zero (E := E) (μ := μ) χ
  let c : ℂ := ∫ y, (b y : ℂ) * (χ y : ℂ) ∂μ
  let e := extChartAt (𝓘(ℝ, E)) (1 : G)
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (1 : G)).mem_nhds (mem_extChartAt_target 1))
  let U := ball (e 1) r
  let L := e.symm '' closedBall (e 1) r
  have hL : IsCompact L := (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm (1 : G)).mono hball)
  let K := L * tsupport b
  have hK : IsCompact K := hL.mul b.hasCompactSupport
  let k : E × G → ℂ := fun p => (b ((e.symm p.1)⁻¹ * p.2) : ℂ)
  have hk : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, ℂ)) ∞ k (U ×ˢ univ) := by
    have he : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ e.symm U :=
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) (1 : G)).mono
        (fun _ hy => hball (ball_subset_closedBall hy))
    have hm : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
        (fun p : E × G => (e.symm p.1)⁻¹ * p.2) (U ×ˢ univ) :=
      ((he.comp contMDiffOn_fst (fun (p : E × G) (hp : p ∈ U ×ˢ univ) => hp.1)).inv.mul
        contMDiffOn_snd)
    exact Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn (b.contMDiff.comp_contMDiffOn hm)
  have hc : Continuous (fun y : G => (χ y : ℂ)) := continuous_subtype_val.comp χ.continuous
  have hs := Integration.Constructions.CharacterTriviality.contDiffOn_weightedIntegral (μ := μ) (H := E) (k := k) isOpen_ball hK hk hc
  have heq (p : E) (hp : p ∈ U) :
      (∫ y in K, (χ y : ℂ) • k (p, y) ∂μ) = (χ (e.symm p) : ℂ) * c := by
    have hsupport : Function.support (fun y => (χ y : ℂ) • k (p, y)) ⊆ K := by
      intro y hy
      have hby : b ((e.symm p)⁻¹ * y) ≠ 0 := by
        intro hz
        apply hy
        simp [k, hz]
      exact ⟨e.symm p, ⟨p, ball_subset_closedBall hp, rfl⟩,
        (e.symm p)⁻¹ * y, subset_tsupport b hby, mul_inv_cancel_left _ _⟩
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by
        by_contra hy'
        exact hy (hsupport hy'))]
    exact character_smoothing_identity (μ := μ) χ b (e.symm p)
  have hsχ : ContDiffOn ℝ ∞ (fun p => (χ (e.symm p) : ℂ)) U := by
    apply (hs.mul (contDiffOn_const (c := c⁻¹))).congr
    intro p hp
    rw [heq p hp]
    exact (mul_inv_cancel_right₀ hb _).symm
  have hat := ((hsχ (e 1) (mem_ball_self hr)).contDiffAt (ball_mem_nhds _ hr)).contMDiffAt.comp
    (1 : G) (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (n := ∞))
  apply hat.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (1 : G)] with y hy
  change (χ y : ℂ) = (χ (e.symm (e y)) : ℂ)
  rw [e.left_inv hy]

include μ in
theorem contMDiff_character (χ : G →ₜ* Circle) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (fun y => (χ y : ℂ)) := by
  intro x
  have h1 := contMDiffAt_character_one (E := E) (μ := μ) χ
  have hx : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞
      (fun y : G => (χ (x⁻¹ * y) : ℂ)) x := by
    apply h1.comp_of_eq (contMDiffAt_const.mul contMDiffAt_id)
    exact inv_mul_cancel x
  have hmul := (((ContinuousLinearMap.mul ℝ ℂ) (χ x : ℂ)).contDiff (n := ∞)).contMDiff.contMDiffAt.comp x hx
  apply hmul.congr_of_eventuallyEq
  filter_upwards [] with y
  change (χ y : ℂ) = (χ x : ℂ) * (χ (x⁻¹ * y) : ℂ)
  simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  exact (mul_inv_cancel_left₀ (Circle.coe_ne_zero _) _).symm

end

end OAI.LieTheory.Semisimple.Regularity.Constructions.CharacterTriviality
