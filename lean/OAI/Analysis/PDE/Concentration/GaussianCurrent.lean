import OAI.Analysis.PDE.Concentration.Current
import OAI.Analysis.PDE.Concentration.WaveBounds
import OAI.Analysis.PDE.Concentration.Packet.Frequency

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem gaussianVelocity_apply {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin d) :
    gaussianVelocity η i = ((gaussianFrequencyK η)⁻¹ * η (some i) : ℝ) := by
  simp [gaussianVelocity, transverseFrequency, Complex.real_smul]

theorem gaussianVelocity_im {d : ℕ} (η : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin d) :
    (gaussianVelocity η i).im = 0 := by
  rw [gaussianVelocity_apply]
  simp

theorem gaussianB0_eq_timeFactor {d : ℕ} (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    gaussianB0 (W, η) = (currentTimeFactor W (gaussianVelocity η)).re := by
  have hi : inner ℝ (gaussianVelocity η) W =
      ∑ i, (W i * gaussianVelocity η i).re := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [gaussianVelocity_apply, real_inner_eq_re_inner (𝕜 := ℂ)]
    simp [RCLike.inner_apply]
  simp [gaussianB0, currentTimeFactor, hi, Complex.div_ofReal_re]

theorem gaussianB1_eq_timeFactor {d : ℕ} (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    gaussianB1 (W, η) = (currentTimeFactor W (gaussianVelocity η)).im := by
  have hi : inner ℝ (Complex.I • gaussianVelocity η) W =
      ∑ i, (W i * gaussianVelocity η i).im := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_eq_re_inner (𝕜 := ℂ)]
    simp [RCLike.inner_apply, gaussianVelocity_apply, Complex.mul_re, Complex.mul_im]
  simp [gaussianB1, currentTimeFactor, hi, Complex.div_ofReal_im]

theorem gaussian_squaredDistance {d : ℕ} (W : TransverseSpace d) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖W - gaussianVelocity η‖ ^ 2 =
      OAI.Analysis.Calculus.Current.squaredDistance W (fun i => (gaussianFrequencyK η)⁻¹ * η (some i)) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [OAI.Analysis.Calculus.Current.squaredDistance]
  apply Finset.sum_congr rfl
  intro i _
  simp [gaussianVelocity_apply]

end OAI.Analysis.PDE.Concentration
