import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerDifferential
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-! # Metric Bounds -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction

noncomputable section

/-! Uniform ellipticity bounds on compact coordinate subsets. -/

open Set
open scoped ContDiff _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {Z : Type*} [TopologicalSpace Z]

/-- A continuous family of positive bilinear forms has a uniform positive
quadratic lower bound on every compact parameter set. -/
theorem positive_bilinear_uniform_lower_bound (B : Z → E →L[ℝ] E →L[ℝ] ℝ)
    {K : Set Z} (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ u : E, c * ‖u‖ * ‖u‖ ≤ B x u u := by
  have hcompact : IsCompact (K ×ˢ Metric.sphere (0 : E) 1) := hK.prod (isCompact_sphere _ _)
  have hBproj : ContinuousOn (fun p : Z × E => B p.1) (K ×ˢ Metric.sphere (0 : E) 1) :=
    hB.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hdiag : ContinuousOn (fun p : Z × E => B p.1 p.2 p.2) (K ×ˢ Metric.sphere (0 : E) 1) :=
    (hBproj.clm_apply continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' hdiag (a := (0 : ℝ)) (by
    intro p hp
    apply hpos p.1 hp.1 p.2
    intro hz
    have hu : ‖p.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    rw [hz, norm_zero] at hu
    exact zero_ne_one hu)
  refine ⟨c, hc, ?_⟩
  intro x hx u
  by_cases hu : u = 0
  · subst u
    simp
  · let v := (‖u‖⁻¹ : ℝ) • u
    have hv : v ∈ Metric.sphere (0 : E) 1 := by
      simpa [v, Metric.mem_sphere] using norm_smul_inv_norm (𝕜 := ℝ) hu
    have hn : ‖u‖ • v = u := by
      change ‖u‖ • ((‖u‖⁻¹ : ℝ) • u) = u
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
    have hg : B x u u = ‖u‖ * ‖u‖ * B x v v := by
      calc
        B x u u = B x (‖u‖ • v) (‖u‖ • v) := by rw [hn]
        _ = ‖u‖ * ‖u‖ * B x v v := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
    calc
      c * ‖u‖ * ‖u‖ = ‖u‖ * ‖u‖ * c := by ring
      _ ≤ ‖u‖ * ‖u‖ * B x v v :=
        mul_le_mul_of_nonneg_left (hbound (x, v) ⟨hx, hv⟩) (mul_self_nonneg _)
      _ = B x u u := hg.symm

omit [ProperSpace E] in
theorem bilinear_uniform_upper_bound (B : Z → E →L[ℝ] E →L[ℝ] ℝ)
    {K : Set Z} (hK : IsCompact K) (hB : ContinuousOn B K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u v : E, |B x u v| ≤ C * ‖u‖ * ‖v‖ := by
  have hnormCont : ContinuousOn (fun x => ‖B x‖) K :=
    (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp_continuousOn hB
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnormCont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx u v
  have hnorm : ‖B x‖ ≤ max C 1 := (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  calc
    |B x u v| = ‖B x u v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B x u‖ * ‖v‖ := (B x u).le_opNorm v
    _ ≤ (‖B x‖ * ‖u‖) * ‖v‖ := mul_le_mul_of_nonneg_right ((B x).le_opNorm u) (norm_nonneg _)
    _ ≤ (max C 1 * ‖u‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)

theorem varietyMetricInChart_uniform_lower_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticModel} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ u : V.analyticModel,
      c * ‖u‖ * ‖u‖ ≤ KahlerDifferential.CM.Construction.varietyMetricInChart V e x u u := by
  exact positive_bilinear_uniform_lower_bound (KahlerDifferential.CM.Construction.varietyMetricInChart V e) hK
    ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).continuousOn.mono hKt)
    (fun x hx u hu => KahlerDifferential.CM.Construction.varietyMetricInChart_positive V e he (hKt hx) u hu)

theorem varietyMetricInChart_uniform_upper_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticModel} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u v : V.analyticModel,
      |KahlerDifferential.CM.Construction.varietyMetricInChart V e x u v| ≤ C * ‖u‖ * ‖v‖ :=
  bilinear_uniform_upper_bound _ hK ((KahlerDifferential.CM.Construction.varietyMetricInChart_smooth V e he).continuousOn.mono hKt)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction
