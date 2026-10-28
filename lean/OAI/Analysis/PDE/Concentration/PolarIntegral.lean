import Mathlib

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter

theorem complex_annulus_integral {f : ℂ → ℝ} (hf : Continuous f)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, f z) =
      ∫ r in a..b, r * ∫ θ in (-Real.pi)..Real.pi, f (Complex.polarCoord.symm (r, θ)) := by
  classical
  let A : Set ℂ := {z | ‖z‖ ∈ Icc a b}
  let T : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b}
  let g : ℝ × ℝ → ℝ := fun p => p.1 * f (Complex.polarCoord.symm p)
  have hAm : MeasurableSet A := measurableSet_Icc.preimage continuous_norm.measurable
  have hTm : MeasurableSet T := measurableSet_Icc.preimage measurable_fst
  have hg : Continuous g := by
    apply continuous_fst.mul
    apply hf.comp
    change Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hpull : (fun p : ℝ × ℝ => p.1 • A.indicator f (Complex.polarCoord.symm p)) =ᵐ[
      volume.restrict polarCoord.target] T.indicator g := by
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    have hpos : 0 < p.1 := hp.1
    have he : Complex.polarCoord.symm p ∈ A ↔ p ∈ T := by
      simp only [A, T, Set.mem_ofPred_eq, Complex.norm_polarCoord_symm, abs_of_pos hpos]
    by_cases hpt : p ∈ T
    · simp only [indicator_of_mem hpt, indicator_of_mem (he.mpr hpt), smul_eq_mul, g]
    · simp only [indicator_of_notMem hpt, indicator_of_notMem (mt he.mp hpt), smul_zero]
  have hset : polarCoord.target ∩ T = Icc a b ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    change ((0 < p.1 ∧ p.2 ∈ Ioo (-Real.pi) Real.pi) ∧ p.1 ∈ Icc a b) ↔
      p.1 ∈ Icc a b ∧ p.2 ∈ Ioo (-Real.pi) Real.pi
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨ha.trans_le h.1.1, h.2⟩, h.1⟩
  have hgi : IntegrableOn g (Icc a b ×ˢ Ioo (-Real.pi) Real.pi) :=
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono_right Ioo_subset_Icc_self)
  calc
    _ = ∫ z, A.indicator f z := (integral_indicator hAm).symm
    _ = ∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target, T.indicator g p := integral_congr_ae hpull
    _ = ∫ p in Icc a b ×ˢ Ioo (-Real.pi) Real.pi, g p := by
      rw [setIntegral_indicator hTm, hset]
    _ = ∫ r in Icc a b, ∫ θ in Ioo (-Real.pi) Real.pi, g (r, θ) := setIntegral_prod g hgi
    _ = ∫ r in a..b, r * ∫ θ in (-Real.pi)..Real.pi, f (Complex.polarCoord.symm (r, θ)) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
      apply intervalIntegral.integral_congr
      intro r _
      change (∫ θ in Ioo (-Real.pi) Real.pi, r * f (Complex.polarCoord.symm (r, θ))) = _
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]

end OAI.Analysis.PDE.Concentration
