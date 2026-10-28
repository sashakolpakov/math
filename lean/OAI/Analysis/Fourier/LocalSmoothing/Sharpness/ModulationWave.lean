import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationData

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

def modulationRemainder {n : ℕ} (N : ℝ) (ω : Space n) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ =>
    Complex.exp (-Complex.I * (t * (‖N • ω + ξ‖ - N) : ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ) x

theorem halfWave_schwartzModulation {n : ℕ} (N : ℝ) (ω : Space n) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (schwartzModulation (N • ω) f) x =
      Complex.exp (Complex.I * (inner ℝ x (N • ω) - t*N : ℝ)) *
        modulationRemainder N ω t f x := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  simp only [angularFourier_schwartzModulation]
  rw [← integral_add_right_eq_self (fun ξ : Space n =>
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
      (Complex.exp (-Complex.I * (t*‖ξ‖:ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ξ-N•ω))) (N•ω)]
  have he (ξ : Space n) :
      Complex.exp (Complex.I * (inner ℝ x (ξ+N•ω) : ℂ)) *
        (Complex.exp (-Complex.I * (t*‖ξ+N•ω‖:ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ξ+N•ω-N•ω)) =
      Complex.exp (Complex.I * (inner ℝ x (N•ω)-t*N:ℝ)) *
        (Complex.exp (Complex.I * (inner ℝ x ξ:ℂ)) *
          (Complex.exp (-Complex.I * (t*(‖N•ω+ξ‖-N):ℝ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)) := by
    rw [add_sub_cancel_right,inner_add_right]
    rw [add_comm ξ (N•ω)]
    simp only [← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  simp only [modulationRemainder,OAI.Analysis.Fourier.LocalSmoothing.angularInverse,Complex.real_smul]
  ring

theorem norm_modulationRemainder {n : ℕ} (N : ℝ) (ω : Space n) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖modulationRemainder N ω t f x‖ =
      ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (schwartzModulation (N•ω) f) x‖ := by
  rw [halfWave_schwartzModulation]
  simp [Complex.norm_exp]

theorem continuous_modulationRemainder {n : ℕ} (N : ℝ) (ω : Space n)
    (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ => modulationRemainder N ω z.2 f z.1) := by
  have hF := OAI.Analysis.Fourier.Restriction.continuous_angularFourier f.integrable
  let H : (Space n × ℝ) → Space n → ℂ := fun z ξ =>
    Complex.exp (Complex.I*(inner ℝ z.1 ξ:ℂ)) *
      (Complex.exp (-Complex.I*(z.2*(‖N•ω+ξ‖-N):ℝ))*OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)
  have hc : Continuous (fun z : Space n × ℝ => ∫ ξ,H z ξ) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖)
    · exact Eventually.of_forall fun y =>
        (by dsimp only [H]; fun_prop : Continuous (H y)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => Eventually.of_forall fun ξ => by
        simp [H,Complex.norm_exp]
    · exact (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f).norm
    · exact Eventually.of_forall fun ξ =>
        (by dsimp only [H]; fun_prop : Continuous (fun y : Space n × ℝ => H y ξ)).tendsto z
  exact hc.const_smul (((2*Real.pi)^n)⁻¹ : ℝ)

theorem tendsto_modulationRemainder {n : ℕ} {ω : Space n} (hω : ‖ω‖=1)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) (x : Space n) :
    Tendsto (fun N : ℝ => modulationRemainder N ω t f x) atTop (𝓝 (f (x-t•ω))) := by
  have hF := OAI.Analysis.Fourier.Restriction.continuous_angularFourier f.integrable
  have hi : Tendsto (fun N : ℝ => ∫ ξ : Space n,
      Complex.exp (Complex.I*(inner ℝ x ξ:ℂ)) *
        (Complex.exp (-Complex.I*(t*(‖N•ω+ξ‖-N):ℝ))*OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)) atTop
      (𝓝 (∫ ξ : Space n, Complex.exp (Complex.I*(inner ℝ (x-t•ω) ξ:ℂ))*OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ‖)
    · exact Eventually.of_forall fun N =>
        (by fun_prop : Continuous (fun ξ : Space n =>
          Complex.exp (Complex.I*(inner ℝ x ξ:ℂ)) *
            (Complex.exp (-Complex.I*(t*(‖N•ω+ξ‖-N):ℝ))*angularFourier f ξ))).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall fun ξ => by
        simp [Complex.norm_exp]
    · exact (OAI.Analysis.Fourier.Restriction.integrable_angularFourier_schwartz f).norm
    · apply Eventually.of_forall
      intro ξ
      have ht := (tendsto_modulation_phase hω ξ).const_mul t
      have hz := (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).const_mul (-Complex.I)
      have hexp := Complex.continuous_exp.continuousAt.tendsto.comp hz
      have h := (hexp.mul_const (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)).const_mul
        (Complex.exp (Complex.I*(inner ℝ x ξ:ℂ)))
      convert h using 1
      congr 1
      rw [← mul_assoc,← Complex.exp_add]
      congr 2
      simp only [inner_sub_left,real_inner_smul_left,Complex.ofReal_sub,Complex.ofReal_mul]
      ring_nf
  have h := hi.const_smul (((2*Real.pi)^n)⁻¹ : ℝ)
  change Tendsto (fun N : ℝ => modulationRemainder N ω t f x) atTop
    (𝓝 (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (x-t•ω))) at h
  rwa [OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz] at h

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
