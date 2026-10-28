import OAI.Analysis.PDE.Concentration.GaussianPhase
import OAI.Analysis.PDE.Concentration.Packet.Frequency

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem norm_packetSpatialFrequency {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (v : Fin d → ℝ) :
    ‖packetSpatialFrequency κ v‖ = κ * (1 + (∑ j, v j * v j) / 2) / Real.sqrt 2 := by
  have hs : 0 ≤ ∑ j, v j * v j := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : (∑ j, (κ * v j) ^ 2) = κ ^ 2 * (∑ j, v j * v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
  change ‖κ * (1 - (∑ j, v j * v j) / 2) / Real.sqrt 2‖ ^ 2 +
    (∑ j, ‖κ * v j‖ ^ 2) = _
  simp only [Real.norm_eq_abs, sq_abs]
  rw [hsum, div_pow, div_pow, hsq]
  ring

theorem gaussianFrequencyK_packet {d : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (v : Fin d → ℝ) :
    gaussianFrequencyK (packetSpatialFrequency κ v) = κ := by
  rw [gaussianFrequencyK, norm_packetSpatialFrequency hκ]
  change (κ * (1 - (∑ j, v j * v j) / 2) / Real.sqrt 2 +
    κ * (1 + (∑ j, v j * v j) / 2) / Real.sqrt 2) / Real.sqrt 2 = κ
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

theorem gaussianFrequencyK_smul {d : ℕ} {h : ℝ} (hh : 0 ≤ h) (η : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    gaussianFrequencyK (h • η) = h * gaussianFrequencyK η := by
  simp only [gaussianFrequencyK, PiLp.smul_apply, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  ring

theorem gaussianVelocity_smul {d : ℕ} {h : ℝ} (hh : h ≠ 0) (hh' : 0 ≤ h)
    (η : OAI.Analysis.Calculus.Current.SpatialSpace d) : gaussianVelocity (h • η) = gaussianVelocity η := by
  rw [gaussianVelocity, gaussianFrequencyK_smul hh', map_smul, mul_inv_rev,
    mul_smul, inv_smul_smul₀ hh]
  rfl

theorem gaussianVelocity_packet {d : ℕ} {κ : ℝ} (hκ : 0 < κ) (v : Fin d → ℝ) :
    gaussianVelocity (packetSpatialFrequency κ v) =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).symm (fun i => (v i : ℂ)) := by
  unfold gaussianVelocity
  rw [gaussianFrequencyK_packet hκ.le]
  ext i
  simp [transverseFrequency, packetSpatialFrequency, Complex.real_smul, hκ.ne']

theorem gaussianVelocity_packet_apply {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (v : Fin d → ℝ) (i : Fin d) : gaussianVelocity (packetSpatialFrequency κ v) i = (v i : ℂ) := by
  rw [gaussianVelocity_packet hκ]
  rfl

end OAI.Analysis.PDE.Concentration
