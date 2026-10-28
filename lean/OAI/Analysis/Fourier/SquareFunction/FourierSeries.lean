import OAI.Analysis.Fourier.SquareFunction.KernelHilbert

open OAI.Analysis.Fourier.Wave

/-! Dominated convergence for actual Fourier integrals, in a form suited
to dyadic multiplier decompositions. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform Filter
open scoped Topology

theorem tendsto_fourierInv_of_dominated {n : ℕ}
    {u : ℕ → Space n → ℂ} {v : Space n → ℂ} {B : Space n → ℝ}
    (hu : ∀ j, AEStronglyMeasurable (u j) volume) (hB : Integrable B)
    (hb : ∀ j, ∀ᵐ ξ ∂volume, ‖u j ξ‖ ≤ B ξ)
    (hv : ∀ᵐ ξ ∂volume, Tendsto (fun j => u j ξ) atTop (𝓝 (v ξ)))
    (x : Space n) : Tendsto (fun j => 𝓕⁻ (u j) x) atTop (𝓝 (𝓕⁻ v x)) := by
  simp only [fourierInv_eq_spatialPhase_smul]
  apply tendsto_integral_of_dominated_convergence B
    (fun j => (continuous_spatialPhase x).aestronglyMeasurable.smul (hu j)) hB
  · intro j
    filter_upwards [hb j] with ξ hξ
    change ‖spatialPhase x ξ • u j ξ‖ ≤ B ξ
    simpa only [Pi.smul_apply, norm_smul, norm_spatialPhase, one_mul] using hξ
  · filter_upwards [hv] with ξ hξ
    exact tendsto_const_nhds.smul hξ

theorem fourierInv_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (u : ι → Space n → ℂ) (hu : ∀ i ∈ s, Integrable (u i))
    (x : Space n) :
    𝓕⁻ (fun ξ => ∑ i ∈ s, u i ξ) x = ∑ i ∈ s, 𝓕⁻ (u i) x := by
  simp only [fourierInv_eq_spatialPhase_smul, smul_eq_mul, Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => integrable_spatialPhase_mul x (hu i hi))

theorem tendsto_sum_fourierInv_of_dominated {n : ℕ}
    {u : ℕ → Space n → ℂ} {v : Space n → ℂ} {B : Space n → ℝ}
    (hu : ∀ j, Integrable (u j)) (hB : Integrable B)
    (hb : ∀ N, ∀ᵐ ξ ∂volume, ‖∑ j ∈ Finset.range N, u j ξ‖ ≤ B ξ)
    (hv : ∀ᵐ ξ ∂volume,
      Tendsto (fun N => ∑ j ∈ Finset.range N, u j ξ) atTop (𝓝 (v ξ)))
    (x : Space n) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, 𝓕⁻ (u j) x) atTop (𝓝 (𝓕⁻ v x)) := by
  have H := tendsto_fourierInv_of_dominated
    (fun N => (MeasureTheory.integrable_finsetSum _ (fun j _ => hu j)).aestronglyMeasurable) hB hb hv x
  simpa only [fourierInv_finset_sum (Finset.range _) u (fun j _ => hu j) x] using H

end OAI.Analysis.Fourier.SquareFunction
