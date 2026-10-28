import OAI.Geometry.Nikodym.Chart.Segments

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal Pointwise
noncomputable section
namespace OAI.Geometry.Nikodym


theorem dilatedTube_subset_smul {n : ℕ} {R : ℝ} (hR : 1≤R)
    (δ : ℝ) (v : Space n) : OAI.MeasureTheory.Kakeya.tube (R*δ) v 0 ⊆ R • OAI.MeasureTheory.Kakeya.tube δ v 0 := by
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  intro x hx
  obtain ⟨t,ht,hxt⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hx
  refine Set.mem_smul_set.mpr ⟨R⁻¹ • x,?_,smul_inv_smul₀ hR0.ne' x⟩
  apply OAI.MeasureTheory.Kakeya.mem_tube_iff.mpr
  refine ⟨t/R,?_,?_⟩
  · apply abs_le.mp
    rw [abs_div,abs_of_pos hR0]
    apply (div_le_iff₀ hR0).mpr
    exact (abs_le.mpr ht).trans (by linarith)
  · have he : R⁻¹•x - ((0:Space n)+(t/R)•v) = R⁻¹•(x-((0:Space n)+t•v)) := by
      simp only [zero_add,smul_sub,smul_smul,div_eq_mul_inv,mul_comm]
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR0)]
    rw [dist_eq_norm] at hxt
    simpa only [← mul_assoc,inv_mul_cancel₀ hR0.ne',one_mul] using
      mul_lt_mul_of_pos_left hxt (inv_pos.mpr hR0)

theorem volume_dilatedTube_le {n : ℕ} {R : ℝ} (hR : 1≤R)
    (δ : ℝ) (v a : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (R*δ) v a) ≤ ENNReal.ofReal (R^n)*volume (OAI.MeasureTheory.Kakeya.tube δ v a) := by
  rw [OAI.MeasureTheory.Kakeya.volume_tube_center_eq,OAI.MeasureTheory.Kakeya.volume_tube_center_eq δ]
  calc
    _ ≤ volume (R • OAI.MeasureTheory.Kakeya.tube δ v 0) := measure_mono (dilatedTube_subset_smul hR δ v)
    _ = _ := by simp [Measure.addHaar_smul,Space,abs_of_pos (lt_of_lt_of_le zero_lt_one hR)]

theorem volume_outerTube_le_innerShortTube {n : ℕ} {R l δ : ℝ}
    (hR : 1≤R) (hl : 0<l) (hl1 : l≤1) (hδ : 0≤δ) (v a : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (R*δ) v a) ≤
      ENNReal.ofReal (R^n*(l^n)⁻¹)*volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) a) := by
  calc
    _ ≤ ENNReal.ofReal (R^n)*volume (OAI.MeasureTheory.Kakeya.tube δ v a) := volume_dilatedTube_le hR δ v a
    _ ≤ ENNReal.ofReal (R^n)*(ENNReal.ofReal ((l^n)⁻¹)*volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) a)) :=
      mul_le_mul' le_rfl (unitTube_volume_le_shortTube hl hl1 hδ v a)
    _ = _ := by rw [ENNReal.ofReal_mul (pow_nonneg (by linarith : 0≤R) n),mul_assoc]

end OAI.Geometry.Nikodym
