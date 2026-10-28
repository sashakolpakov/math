import OAI.Geometry.Nikodym.Definitions
import OAI.MeasureTheory.Kakeya.DirectionNets

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal Pointwise
noncomputable section
namespace OAI.Geometry.Nikodym


theorem shortSegment_subset_unitSegment {n : ℕ} {l : ℝ} (hl : 0≤l) (hl1 : l≤1)
    (v a : Space n) : OAI.MeasureTheory.Kakeya.unitSegment (l•v) a ⊆ OAI.MeasureTheory.Kakeya.unitSegment v a := by
  rintro x ⟨t,ht,rfl⟩
  refine ⟨t*l,?_,?_⟩
  · have H : |t*l|≤(1/2:ℝ) := by
      rw [abs_mul,abs_of_nonneg hl]
      exact (mul_le_mul_of_nonneg_right (abs_le.mpr ht) hl).trans (by nlinarith)
    exact abs_le.mp H
  · simp only [smul_smul]

theorem shortTube_subset_unitTube {n : ℕ} {l : ℝ} (hl : 0≤l) (hl1 : l≤1)
    (δ : ℝ) (v a : Space n) : OAI.MeasureTheory.Kakeya.tube δ (l•v) a ⊆ OAI.MeasureTheory.Kakeya.tube δ v a := by
  intro x hx
  obtain ⟨t,ht,hxt⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hx
  obtain ⟨s,hs,he⟩ := shortSegment_subset_unitSegment hl hl1 v a ⟨t,ht,rfl⟩
  exact OAI.MeasureTheory.Kakeya.mem_tube_iff.mpr ⟨s,hs,he ▸ hxt⟩

theorem smul_unitTube_subset_shortTube {n : ℕ} {l δ : ℝ}
    (hl : 0<l) (hl1 : l≤1) (hδ : 0≤δ) (v : Space n) :
    l • OAI.MeasureTheory.Kakeya.tube δ v 0 ⊆ OAI.MeasureTheory.Kakeya.tube δ (l•v) 0 := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨t,ht,hxt⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hx
  apply OAI.MeasureTheory.Kakeya.mem_tube_iff.mpr
  refine ⟨t,ht,?_⟩
  have he : l•x - ((0:Space n)+t•(l•v)) = l•(x-((0:Space n)+t•v)) := by
    simp only [zero_add,smul_sub,smul_smul]
    rw [mul_comm l t]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos hl]
  rw [dist_eq_norm] at hxt
  exact (mul_lt_mul_of_pos_left hxt hl).trans_le (by nlinarith)

theorem unitTube_volume_le_shortTube {n : ℕ} {l δ : ℝ}
    (hl : 0<l) (hl1 : l≤1) (hδ : 0≤δ) (v a : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ v a) ≤ ENNReal.ofReal ((l^n)⁻¹) * volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) a) := by
  rw [OAI.MeasureTheory.Kakeya.volume_tube_center_eq,OAI.MeasureTheory.Kakeya.volume_tube_center_eq δ (l•v)]
  have h : volume (l • OAI.MeasureTheory.Kakeya.tube δ v 0) ≤ volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) 0) :=
    measure_mono (smul_unitTube_subset_shortTube hl hl1 hδ v)
  have he : volume (l • OAI.MeasureTheory.Kakeya.tube δ v 0) = ENNReal.ofReal (l^n)*volume (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
    simp [Measure.addHaar_smul,Space,abs_of_pos hl]
  rw [he] at h
  have H := mul_le_mul' (le_refl (ENNReal.ofReal ((l^n)⁻¹))) h
  have hp : 0<l^n := pow_pos hl n
  simpa only [← mul_assoc,← ENNReal.ofReal_mul (inv_pos.mpr hp).le,
    inv_mul_cancel₀ hp.ne',ENNReal.ofReal_one,one_mul] using H

/-- A segment whose length lies in a fixed positive interval has its
normalized tube average controlled by the genuine unit Nikodym operator. -/
theorem shortTube_average_le_nikodym {n : ℕ} {l δ : ℝ}
    (hl : 0<l) (hl1 : l≤1) (hδ : 0<δ) (f : Space n → ℂ)
    {v a x : Space n} (hv : ‖v‖=1) (hx : x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) a) :
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ (l•v) a,‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) a) ≤
      ENNReal.ofReal ((l^n)⁻¹) * nikodymMaximal δ f x := by
  calc
    _ ≤ ENNReal.ofReal ((l^n)⁻¹) *
        ((∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ v a,‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ v a)) := by
      apply OAI.MeasureTheory.Kakeya.ennreal_div_le_mul_div
        (OAI.MeasureTheory.Kakeya.volume_tube_pos hδ (l•v) a).ne' (OAI.MeasureTheory.Kakeya.volume_tube_lt_top δ (l•v) a).ne
        (OAI.MeasureTheory.Kakeya.volume_tube_pos hδ v a).ne' (OAI.MeasureTheory.Kakeya.volume_tube_lt_top δ v a).ne
      · exact lintegral_mono_set (shortTube_subset_unitTube hl.le hl1 δ v a)
      · exact unitTube_volume_le_shortTube hl hl1 hδ.le v a
    _ ≤ _ := mul_le_mul' le_rfl
      (tube_average_le_nikodymMaximal f hv (shortSegment_subset_unitSegment hl.le hl1 v a hx))

theorem shortTube_average_le_nikodym_uniform {n : ℕ} {a l δ : ℝ}
    (ha : 0<a) (hal : a≤l) (hl1 : l≤1) (hδ : 0<δ) (f : Space n → ℂ)
    {v c x : Space n} (hv : ‖v‖=1) (hx : x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) c) :
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ (l•v) c,‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ (l•v) c) ≤
      ENNReal.ofReal ((a^n)⁻¹) * nikodymMaximal δ f x := by
  apply (shortTube_average_le_nikodym (ha.trans_le hal) hl1 hδ f hv hx).trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  simpa only [one_div] using one_div_le_one_div_of_le (pow_pos ha n)
    (pow_le_pow_left₀ ha.le hal n)

end OAI.Geometry.Nikodym
