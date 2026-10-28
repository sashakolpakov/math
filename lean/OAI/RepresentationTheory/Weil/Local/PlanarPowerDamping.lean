import OAI.RepresentationTheory.Weil.Local.PlanarRadialIntegral
import OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase
import OAI.RepresentationTheory.Weil.Local.RealPower

/-! # Planar Power Damping -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping.Construction

noncomputable section

/-! Integrability and local convergence of the actual complex norm-power damping. -/

open _root_.MeasureTheory Filter Set
open scoped _root_.Topology

def planarPowerDamping (s ε b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) : ℂ) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z

theorem planarPowerDamping_norm (s ε b : ℝ) (z : ℝ × ℝ) :
    ‖planarPowerDamping s ε b z‖ = Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) := by
  rw [planarPowerDamping, norm_mul, PlanarQuadraticPhase.Construction.planarQuadraticPhase_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem planarPowerDamping_continuous (s ε b : ℝ) (hs : 0 < s) :
    Continuous (planarPowerDamping s ε b) := by
  have ht : Continuous PlanarRadialCompact.Construction.planarRadiusSquared := by unfold PlanarRadialCompact.Construction.planarRadiusSquared; fun_prop
  have he := ((ht.rpow_const (fun _ => Or.inr hs.le)).const_mul (-ε)).rexp
  exact (Complex.continuous_ofReal.comp he).mul (PlanarQuadraticPhase.Construction.planarQuadraticPhase_continuous b)

theorem planar_power_weight_integrable (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (fun z : ℝ × ℝ => (Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) : ℂ)) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-ε * t ^ s)) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hs hε
  exact PlanarRadialIntegral.Construction.planarRadial_integrable (fun t => (Real.exp (-ε * t ^ s) : ℂ)) hi.ofReal

theorem planarPowerDamping_integrable (s ε b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (planarPowerDamping s ε b) := by
  apply (planar_power_weight_integrable s ε hs hε).norm.mono'
    (planarPowerDamping_continuous s ε b hs).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [planarPowerDamping_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem planarPowerDamping_norm_le (s ε b : ℝ) (hε : 0 ≤ ε) (z : ℝ × ℝ) :
    ‖planarPowerDamping s ε b z‖ ≤ 1 := by
  rw [planarPowerDamping_norm, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε)
    (Real.rpow_nonneg (PlanarRadialCompact.Construction.planarRadiusSquared_nonneg z) s)

theorem planarPowerDamping_tendsto (s b : ℝ) (z : ℝ × ℝ) :
    Tendsto (fun ε => planarPowerDamping s ε b z) (𝓝[>] (0 : ℝ)) (𝓝 (PlanarQuadraticPhase.Construction.planarQuadraticPhase b z)) := by
  have hc : ContinuousAt (fun ε => planarPowerDamping s ε b z) 0 := by
    unfold planarPowerDamping
    fun_prop
  simpa only [planarPowerDamping, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem planarPowerDamping_complex (s ε : ℝ) (z : ℂ) :
    planarPowerDamping s ε Real.pi (z.re, z.im) =
      (Real.exp (-ε * ‖z‖ ^ (2 * s)) : ℂ) * ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) := by
  rw [planarPowerDamping, PlanarQuadraticPhase.Construction.planarQuadraticPhase_standard]
  have hnorm : PlanarRadialCompact.Construction.planarRadiusSquared (z.re, z.im) = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp [PlanarRadialCompact.Construction.planarRadiusSquared, Complex.normSq_apply, pow_two]
  rw [hnorm, Real.rpow_mul (norm_nonneg z), Real.rpow_two]

end

end OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping.Construction
