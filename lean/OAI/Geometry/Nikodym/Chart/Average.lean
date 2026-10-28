import OAI.Geometry.Nikodym.Chart.Radius
import OAI.Geometry.Nikodym.Chart.Measure

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Geometry.Nikodym


theorem lintegral_restrict_le_of_measure_le {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {b : ℝ≥0∞} (h : μ≤b • ν) (T : Set X)
    (f : X → ℝ≥0∞) :
    (∫⁻ x in T,f x ∂μ) ≤ b * ∫⁻ x in T,f x ∂ν := by
  calc
    _ ≤ ∫⁻ x,f x ∂((b • ν).restrict T) :=
      lintegral_mono' (Measure.restrict_mono_measure h T) le_rfl
    _ = _ := by rw [Measure.restrict_smul,lintegral_smul_measure]; rfl

/-- Measure comparison for a chart is needed only on its actual image. -/
theorem measure_inner_le {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {a : ℝ≥0∞} {V I T : Set X}
    (hI : MeasurableSet I) (hIV : I⊆V) (hIT : I⊆T)
    (h : μ.restrict V≤a • ν) : μ I ≤ a * ν T := by
  have H := Measure.le_iff'.mp h I
  rw [Measure.restrict_apply hI,inter_eq_left.mpr hIV,Measure.smul_apply] at H
  exact H.trans (mul_le_mul' le_rfl (measure_mono hIT))

/-- A measurable majorant for an arbitrary straightened geodesic tube.
The inner tube lying in `V` is the explicit chart-margin requirement. -/
theorem chartTube_average_le_nikodym {n : ℕ} {ν : Measure (Space n)}
    {V T : Set (Space n)} {a b : ℝ≥0∞}
    (_ : a≠⊤) (hb : b≠⊤)
    (hup : ν≤b • volume) (hdown : volume.restrict V≤a • ν)
    {r R l l₀ : ℝ} (hr : 0<r) (hR : 1≤R)
    (hl₀ : 0<l₀) (hl : l₀≤l) (hl1 : l≤1)
    {v c x : Space n} (hv : ‖v‖=1) (hx : x∈OAI.MeasureTheory.Kakeya.unitSegment (l•v) c)
    (hinner : OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆T) (hmargin : OAI.MeasureTheory.Kakeya.tube r (l•v) c⊆V)
    (houter : T⊆OAI.MeasureTheory.Kakeya.tube (R*r) v c) (f : Space n → ℂ) :
    (∫⁻ y in T,‖f y‖ₑ ∂ν) / ν T ≤
      (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹)) * nikodymMaximal (R*r) f x := by
  have hlpos := hl₀.trans_le hl
  have hRpos : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hden := measure_inner_le (OAI.MeasureTheory.Kakeya.measurableSet_tube r (l•v) c) hmargin hinner hdown
  have hT0 : ν T≠0 := by
    intro h
    rw [h,mul_zero] at hden
    exact (OAI.MeasureTheory.Kakeya.volume_tube_pos hr (l•v) c).not_ge hden
  have hTtop : ν T≠⊤ := by
    have H := (Measure.le_iff'.mp hup T).trans
      (mul_le_mul' le_rfl (measure_mono houter))
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hb
      (OAI.MeasureTheory.Kakeya.volume_tube_lt_top (R*r) v c).ne) H
  have hvol : volume (OAI.MeasureTheory.Kakeya.tube (R*r) v c) ≤
      (ENNReal.ofReal (R^n*(l₀^n)⁻¹)*a)*ν T := by
    have hlpow : (l^n)⁻¹≤(l₀^n)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hl₀ n)
        (pow_le_pow_left₀ hl₀.le hl n)
    calc
      _ ≤ ENNReal.ofReal (R^n*(l^n)⁻¹)*volume (OAI.MeasureTheory.Kakeya.tube r (l•v) c) :=
        volume_outerTube_le_innerShortTube hR hlpos hl1 hr.le v c
      _ ≤ ENNReal.ofReal (R^n*(l₀^n)⁻¹)*volume (OAI.MeasureTheory.Kakeya.tube r (l•v) c) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hlpow (pow_nonneg hRpos.le n))) le_rfl
      _ ≤ ENNReal.ofReal (R^n*(l₀^n)⁻¹)*(a*ν T) := mul_le_mul' le_rfl hden
      _ = _ := (mul_assoc _ _ _).symm
  have hnum : (∫⁻ y in T,‖f y‖ₑ ∂ν) ≤ b*∫⁻ y in OAI.MeasureTheory.Kakeya.tube (R*r) v c,‖f y‖ₑ :=
    (lintegral_restrict_le_of_measure_le hup T _).trans
      (mul_le_mul' le_rfl (lintegral_mono_set houter))
  have H := OAI.MeasureTheory.Kakeya.ennreal_div_le_mul_div hT0 hTtop
    (OAI.MeasureTheory.Kakeya.volume_tube_pos (mul_pos hRpos hr) v c).ne'
    (OAI.MeasureTheory.Kakeya.volume_tube_lt_top (R*r) v c).ne hnum hvol
  have HN := tube_average_le_nikodymMaximal (δ := R*r) f hv
    (shortSegment_subset_unitSegment hlpos.le hl1 v c hx)
  calc
    _ ≤ (ENNReal.ofReal (R^n*(l₀^n)⁻¹)*a) *
        ((b*∫⁻ y in OAI.MeasureTheory.Kakeya.tube (R*r) v c,‖f y‖ₑ)/volume (OAI.MeasureTheory.Kakeya.tube (R*r) v c)) := H
    _ = (a*b*ENNReal.ofReal (R^n*(l₀^n)⁻¹))*
        ((∫⁻ y in OAI.MeasureTheory.Kakeya.tube (R*r) v c,‖f y‖ₑ)/volume (OAI.MeasureTheory.Kakeya.tube (R*r) v c)) := by
      simp only [div_eq_mul_inv]; ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl HN

end OAI.Geometry.Nikodym
