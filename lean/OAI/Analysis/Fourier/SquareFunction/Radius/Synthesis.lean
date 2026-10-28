import OAI.Analysis.Fourier.SquareFunction.CountableSquare

/-! Infinite synthesis in the mixed radius/dyadic-scale square norm. The
argument only needs almost-everywhere convergence of finite partial sums. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Filter
open scoped ENNReal Topology

theorem eLpNorm_le_tsum_of_tendsto_sum {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u : ℕ → X → E} {v : X → E}
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) (hv : AEStronglyMeasurable v μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun N => ∑ j ∈ Finset.range N, u j x)
      atTop (𝓝 (v x))) :
    eLpNorm v p μ ≤ ∑' j, eLpNorm (u j) p μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto (f := fun N x => ∑ j ∈ Finset.range N, u j x)
    (Filter.Eventually.of_forall fun N => ?_)
    (fun N => by fun_prop) hv hlim
  have he : (fun x => ∑ j ∈ Finset.range N, u j x) = ∑ j ∈ Finset.range N, u j := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact (eLpNorm_sum_le (s := Finset.range N) hp).trans (ENNReal.sum_le_tsum _)

theorem eLpNorm_count_two (a : ℤ → ℝ≥0∞) :
    eLpNorm a 2 Measure.count = (∑' k, a k ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_of_countable a).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self, lintegral_count]

noncomputable def dyadicRadiusNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : ℤ → X → ℂ) : ℝ≥0∞ :=
  (∑' k, eLpNorm (u k) 2 μ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

theorem dyadicRadiusNorm_le_tsum {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : ℕ → ℤ → X → ℂ} {v : ℤ → X → ℂ}
    (hu : ∀ j k, AEStronglyMeasurable (u j k) μ)
    (hv : ∀ k, AEStronglyMeasurable (v k) μ)
    (hlim : ∀ k, ∀ᵐ x ∂μ, Tendsto (fun N => ∑ j ∈ Finset.range N, u j k x)
      atTop (𝓝 (v k x))) :
    dyadicRadiusNorm μ v ≤ ∑' j, dyadicRadiusNorm μ (u j) := by
  have hb (k : ℤ) : eLpNorm (v k) 2 μ ≤ ∑' j, eLpNorm (u j k) 2 μ :=
    eLpNorm_le_tsum_of_tendsto_sum (fun j => hu j k) (hv k) (by norm_num) (hlim k)
  calc
    _ ≤ (∑' k, (∑' j, eLpNorm (u j k) 2 μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact ENNReal.tsum_le_tsum (fun k => ENNReal.rpow_le_rpow (hb k) (by norm_num))
    _ = eLpNorm (fun k => ∑' j, eLpNorm (u j k) 2 μ) 2 Measure.count :=
      (eLpNorm_count_two _).symm
    _ ≤ ∑' j, eLpNorm (fun k => eLpNorm (u j k) 2 μ) 2 Measure.count := by
      simpa only [ENNReal.ofReal_ofNat] using
        (ennreal_eLpNorm_tsum_le (μ := Measure.count)
          (fun j => measurable_of_countable (fun k => eLpNorm (u j k) 2 μ))
          (p := 2) (by norm_num))
    _ = _ := by
      apply tsum_congr
      intro j
      exact eLpNorm_count_two _

theorem dyadicRadiusNorm_congr_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v : ℤ → X → ℂ} (he : ∀ k, u k =ᵐ[μ] v k) :
    dyadicRadiusNorm μ u = dyadicRadiusNorm μ v := by
  unfold dyadicRadiusNorm
  congr 1
  apply tsum_congr
  intro k
  rw [eLpNorm_congr_ae (he k)]

theorem dyadicRadiusNorm_add_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u v : ℤ → X → ℂ) :
    dyadicRadiusNorm μ (fun k x => u k x + v k x) ≤
      dyadicRadiusNorm μ u + dyadicRadiusNorm μ v := by
  have hb (k : ℤ) : eLpNorm (fun x => u k x + v k x) 2 μ ≤
      eLpNorm (u k) 2 μ + eLpNorm (v k) 2 μ := eLpNorm_add_le (by norm_num)
  calc
    _ ≤ (∑' k, (eLpNorm (u k) 2 μ + eLpNorm (v k) 2 μ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact ENNReal.tsum_le_tsum (fun k => ENNReal.rpow_le_rpow (hb k) (by norm_num))
    _ = eLpNorm (fun k => eLpNorm (u k) 2 μ + eLpNorm (v k) 2 μ) 2 Measure.count :=
      (eLpNorm_count_two _).symm
    _ ≤ eLpNorm (fun k => eLpNorm (u k) 2 μ) 2 Measure.count +
        eLpNorm (fun k => eLpNorm (v k) 2 μ) 2 Measure.count := eLpNorm_add_le (by norm_num)
    _ = _ := by rw [eLpNorm_count_two, eLpNorm_count_two]; rfl

end OAI.Analysis.Fourier.SquareFunction
