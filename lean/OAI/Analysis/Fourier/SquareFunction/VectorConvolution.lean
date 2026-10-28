import OAI.Analysis.Fourier.SquareFunction.KernelHilbert

open OAI.Analysis.Fourier.Wave

/-! Fourier inversion and convolution for an integrable Banach-valued symbol.
The interchange is justified on the full product space. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform

theorem spatialPhase_sub {n : ℕ} (x y ξ : Space n) :
    spatialPhase x ξ * spatialPhase (-y) ξ = spatialPhase (x - y) ξ := by
  unfold spatialPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_neg_right, inner_sub_right]
  push_cast
  ring

theorem fourier_eq_negative_spatialPhase {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    𝓕 f ξ = ∫ y, spatialPhase (-y) ξ * f y := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [spatialPhase, inner_neg_right, smul_eq_mul]
    congr 2
    push_cast
    rw [real_inner_comm ξ y]
    ring

theorem inverseFourier_smul_eq_convolve {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {m : Space n → E} {f : Space n → ℂ} (hm : Integrable m) (hf : Integrable f)
    (x : Space n) :
    Integrable (fun y => f y • 𝓕⁻ m (x - y)) ∧
      𝓕⁻ (fun ξ => 𝓕 f ξ • m ξ) x = convolveKernel (𝓕⁻ m) f x := by
  let G : Space n × Space n → E := fun z =>
    spatialPhase (x - z.2) z.1 • (f z.2 • m z.1)
  have hphase : Continuous (fun z : Space n × Space n => spatialPhase (x - z.2) z.1) := by
    unfold spatialPhase
    fun_prop
  have hG : Integrable G (volume.prod volume) := by
    apply (hm.norm.mul_prod hf.norm).mono
      (hphase.aestronglyMeasurable.smul
        (hf.aestronglyMeasurable.comp_snd.smul hm.aestronglyMeasurable.comp_fst))
    exact Filter.Eventually.of_forall fun z => by
      change ‖spatialPhase (x - z.2) z.1 • (f z.2 • m z.1)‖ ≤ ‖‖m z.1‖ * ‖f z.2‖‖
      simp only [norm_smul, norm_spatialPhase, Real.norm_eq_abs,
        abs_mul, abs_norm, mul_comm, mul_one, le_refl]
  have hinner (y : Space n) : (∫ ξ, G (ξ, y)) = f y • 𝓕⁻ m (x - y) := by
    rw [fourierInv_eq_spatialPhase_smul]
    simp_rw [G, smul_comm (spatialPhase (x - y) _) (f y)]
    exact integral_smul _ _
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hG.integral_prod_right
  · rw [fourierInv_eq_spatialPhase_smul]
    trans ∫ ξ, ∫ y, G (ξ, y)
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only
        rw [fourier_eq_negative_spatialPhase, ← integral_smul_const, ← integral_smul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          dsimp only [G]
          rw [mul_smul, ← smul_assoc, smul_eq_mul, spatialPhase_sub]
    · rw [integral_integral_swap hG]
      exact integral_congr_ae (Filter.Eventually.of_forall hinner)

end OAI.Analysis.Fourier.SquareFunction
