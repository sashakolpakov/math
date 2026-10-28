import OAI.Analysis.Fourier.BochnerRiesz.UniformConvergence

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


theorem bochnerRieszIndex_ofReal {n : ℕ} {p : ℝ} (hp : 0 ≤ p) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) = max ((n : ℝ) * |p⁻¹ - 1 / 2| - 1 / 2) 0 := by
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp]

theorem exists_lower_bochnerRiesz_exponent {n : ℕ} {p δ : ℝ}
    (hp : 1 < p) (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) < δ) :
    ∃ q : ℝ, 1 < q ∧ q < p ∧ OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal q) < δ := by
  let F : ℝ → ℝ := fun q => max ((n : ℝ) * |q⁻¹ - 1 / 2| - 1 / 2) 0
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hc : ContinuousAt F p := by
    exact ((continuousAt_const.mul ((continuousAt_id.inv₀ hp0.ne').sub
      continuousAt_const).abs).sub continuousAt_const).max continuousAt_const
  have hFp : F p < δ := by rwa [bochnerRieszIndex_ofReal hp0.le] at hδ
  have he : ∀ᶠ q in 𝓝 p, F q < δ := hc.tendsto.eventually (eventually_lt_nhds hFp)
  obtain ⟨ε, hε, heε⟩ := Metric.eventually_nhds_iff.mp he
  let d := min ((p - 1) / 2) (ε / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hd1 : d ≤ (p - 1) / 2 := min_le_left _ _
  have hdε : d ≤ ε / 2 := min_le_right _ _
  have hq : 1 < p - d := by linarith
  refine ⟨p - d, hq, by linarith, ?_⟩
  rw [bochnerRieszIndex_ofReal (by linarith : 0 ≤ p - d)]
  apply heε
  rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
  linarith

/-- Norm convergence on the dense Schwartz core, throughout the open finite
Bochner--Riesz range. -/
theorem localSmoothing_bochnerRiesz_schwartz_norm_convergence (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 < p)
    (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n (ENNReal.ofReal p) < δ) (f : SchwartzMap (Space n) ℂ) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x - f x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨q, hq, hqp, hqδ⟩ := exists_lower_bochnerRiesz_exponent hp hδ
  obtain ⟨C, hC, hbound⟩ := OAI.Analysis.Fourier.Radial.localSmoothing_bochnerRieszConjecture hls n hn
    (ENNReal.ofReal q) (by simpa using ENNReal.ofReal_le_ofReal hq.le) δ hqδ
  exact tendsto_eLpNorm_bochnerRiesz_sub_of_lower_bound
    ((le_max_right _ _).trans hδ.le) hq.le hqp f hC.le (fun R hR => (hbound R hR f).2)

/-- Uniform boundedness extends strong convergence from a dense core. -/
theorem tendsto_operators_of_dense_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι α : Type*} {l : Filter ι} {e : α → E} (he : DenseRange e)
    (T : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hc : ∀ a, Tendsto (fun i => T i (e a)) l (𝓝 (e a))) (x : E) :
    Tendsto (fun i => T i x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (3 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨y, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp (he x) η hη
  have ha'' : ‖x - e a‖ ≤ η := le_of_lt (by simpa only [dist_eq_norm] using ha)
  have ha' : ‖e a - x‖ ≤ η := by simpa only [norm_sub_rev] using ha''
  have hmid := (Metric.tendsto_nhds.mp (hc a)) (ε / 3) (by positivity)
  filter_upwards [hT, hmid] with i hi hmid
  rw [dist_eq_norm] at hmid ⊢
  have hfirst : ‖T i (x - e a)‖ ≤ C * η :=
    ((T i).le_opNorm _).trans (mul_le_mul hi ha'' (norm_nonneg _) hC)
  have hnorm : ‖T i x - x‖ ≤ ‖T i (x - e a)‖ + ‖T i (e a) - e a‖ + ‖e a - x‖ := by
    calc
      _ = ‖T i (x - e a) + (T i (e a) - e a) + (e a - x)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hηeq : (C + 1) * η = ε / 3 := by
    dsimp [η]
    field_simp
  nlinarith

end OAI.Analysis.Fourier.BochnerRiesz
