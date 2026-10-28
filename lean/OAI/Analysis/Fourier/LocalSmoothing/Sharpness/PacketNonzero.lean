import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularPacket

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open _root_.MeasureTheory Set
open scoped ENNReal

theorem focusing_packet_ne_zero {n : ℕ} (hn : 1 ≤ n) {N t₀ : ℝ} (hN : 0 < N)
    {f : SchwartzMap (Space n) ℂ}
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N t₀ ξ) : f ≠ 0 := by
  let ω : Space n := EuclideanSpace.single ⟨0,by omega⟩ 1
  have hω : ‖ω‖ = 1 := by simp [ω]
  let ξ : Space n := (N*(3/2:ℝ)) • ω
  have hnorm : ‖N⁻¹ • ξ‖ = 3/2 := by
    dsimp [ξ]
    rw [smul_smul,inv_mul_cancel_left₀ hN.ne',norm_smul,hω,mul_one]
    norm_num
  have hb : radialBump (3/2) = 1 := radialBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall,dist_self,radialBump]
    norm_num)
  have hs : radialSymbol n (N⁻¹ • ξ) = 1 := by simp only [radialSymbol,hnorm,hb,Complex.ofReal_one]
  have hnz : focusingSymbol n N t₀ ξ ≠ 0 := by
    rw [focusingSymbol,hs,mul_one]
    exact Complex.exp_ne_zero _
  intro hz
  have h := hf ξ
  rw [hz] at h
  exact hnz (by simpa [OAI.Analysis.Fourier.LocalSmoothing.angularFourier] using h.symm)

theorem schwartz_eLpNorm_ne_zero {n : ℕ} {f : SchwartzMap (Space n) ℂ}
    (hf : f ≠ 0) {p : ℝ≥0∞} (hp : p ≠ 0) : eLpNorm f p volume ≠ 0 := by
  intro hz
  have hae := (eLpNorm_eq_zero_iff hp).mp hz
  have he := (Continuous.ae_eq_iff_eq volume f.continuous continuous_const).mp hae
  apply hf
  ext x
  exact congrFun he x

theorem focusing_packet_tsupport {n : ℕ} {N t₀ : ℝ} (hN : 0 < N)
    {f : SchwartzMap (Space n) ℂ}
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N t₀ ξ) :
    tsupport (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) ⊆ {ξ | N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N} := by
  apply closure_minimal (focusing_packet_annular hN hf)
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
