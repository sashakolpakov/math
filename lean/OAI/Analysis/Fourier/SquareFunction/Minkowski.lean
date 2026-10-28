import OAI.Analysis.Fourier.SquareFunction.VectorMaximal
import OAI.Analysis.Fourier.WavePackets.Young

/-! Weighted integral synthesis for Hilbert-valued shell families. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

/-- A weighted average of uniformly bounded `Lᵖ` slices has the expected
`Lᵖ` bound. The domination formulation also applies to integrals represented
in a different Banach space. -/
theorem eLpNorm_weighted_integral_domination
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] [NormedAddCommGroup G]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {F : X × Y → H} (hF : Measurable F)
    {κ : Y → ℝ≥0∞} (hκ : Measurable κ)
    {T : X → G} (hT : AEStronglyMeasurable T μ)
    {p : ℝ} (hp : 1 ≤ p) {B : ℝ≥0∞}
    (hbound : ∀ y, eLpNorm (fun x => F (x, y)) (ENNReal.ofReal p) μ ≤ B)
    (hdom : ∀ x, ‖T x‖ₑ ≤ ∫⁻ y, κ y * ‖F (x, y)‖ₑ ∂ν) :
    eLpNorm T (ENNReal.ofReal p) μ ≤ (∫⁻ y, κ y ∂ν) * B := by
  have hp0 : 0 < p := by linarith
  have hFx (y : Y) : Measurable (fun x => F (x, y)) :=
    hF.comp (measurable_id.prodMk measurable_const)
  have hFy (x : X) : Measurable (fun y => F (x, y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hslice (y : Y) : (∫⁻ x, ‖F (x, y)‖ₑ ^ p ∂μ) ≤ B ^ p := by
    rw [← eLpNorm_rpow_eq_moment μ (hFx y).aestronglyMeasurable hp0]
    exact ENNReal.rpow_le_rpow (hbound y) hp0.le
  have hpoint (x : X) : ‖T x‖ₑ ^ p ≤
      (∫⁻ y, κ y ∂ν) ^ (p - 1) * ∫⁻ y, κ y * ‖F (x, y)‖ₑ ^ p ∂ν := by
    apply (ENNReal.rpow_le_rpow (hdom x) hp0.le).trans
    exact OAI.Analysis.Fourier.WavePackets.lintegral_weighted_rpow_le hκ (hFy x).enorm hp
  have hm : Measurable (fun z : X × Y => κ z.2 * ‖F z‖ₑ ^ p) :=
    (hκ.comp measurable_snd).mul (hF.enorm.pow_const p)
  have hi : (∫⁻ x, ‖T x‖ₑ ^ p ∂μ) ≤ (∫⁻ y, κ y ∂ν) ^ p * B ^ p := by
    calc
      _ ≤ ∫⁻ x, (∫⁻ y, κ y ∂ν) ^ (p - 1) *
          (∫⁻ y, κ y * ‖F (x, y)‖ₑ ^ p ∂ν) ∂μ := lintegral_mono hpoint
      _ = (∫⁻ y, κ y ∂ν) ^ (p - 1) *
          (∫⁻ x, ∫⁻ y, κ y * ‖F (x, y)‖ₑ ^ p ∂ν ∂μ) :=
        lintegral_const_mul'' _ hm.lintegral_prod_right.aemeasurable
      _ = (∫⁻ y, κ y ∂ν) ^ (p - 1) *
          (∫⁻ y, ∫⁻ x, κ y * ‖F (x, y)‖ₑ ^ p ∂μ ∂ν) := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
      _ ≤ (∫⁻ y, κ y ∂ν) ^ (p - 1) * (∫⁻ y, κ y * B ^ p ∂ν) := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono
        intro y
        dsimp only
        rw [lintegral_const_mul'' _ ((hFx y).enorm.pow_const p).aemeasurable]
        exact mul_le_mul' le_rfl (hslice y)
      _ = (∫⁻ y, κ y ∂ν) ^ (p - 1) * ((∫⁻ y, κ y ∂ν) * B ^ p) := by
        rw [lintegral_mul_const'' _ hκ.aemeasurable]
      _ = _ := by
        rw [← mul_assoc]
        congr 1
        calc
          _ = (∫⁻ y, κ y ∂ν) ^ (p - 1) * (∫⁻ y, κ y ∂ν) ^ (1 : ℝ) := by
            rw [ENNReal.rpow_one]
          _ = (∫⁻ y, κ y ∂ν) ^ (p - 1 + 1) :=
            (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hp) zero_le_one).symm
          _ = _ := by congr 1; ring
  rw [← eLpNorm_rpow_eq_moment μ hT hp0] at hi
  have hroot := ENNReal.rpow_le_rpow hi (by positivity : 0 ≤ 1 / p)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using hroot

/-- An integrable majorant for the norms of the slices controls their
Bochner integral. This form does not require measurability into an `Lp`+quotient, only joint measurability of the representatives. -/
theorem eLpNorm_integral_domination_of_slice_bound
    {X Y H G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] [NormedAddCommGroup G]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {F : X × Y → H} (hF : Measurable F)
    {w : Y → ℝ} (hw : Measurable w) (hwpos : ∀ y, 0 < w y)
    {T : X → G} (hT : AEStronglyMeasurable T μ)
    {p : ℝ} (hp : 1 ≤ p) {B : ℝ≥0∞}
    (hbound : ∀ y, eLpNorm (fun x => F (x, y)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (w y) * B)
    (hdom : ∀ x, ‖T x‖ₑ ≤ ∫⁻ y, ‖F (x, y)‖ₑ ∂ν) :
    eLpNorm T (ENNReal.ofReal p) μ ≤ (∫⁻ y, ENNReal.ofReal (w y) ∂ν) * B := by
  let F₀ : X × Y → H := fun z => (w z.2)⁻¹ • F z
  have hF₀ : Measurable F₀ := (hw.comp measurable_snd).inv.smul hF
  have hid (y : Y) : ENNReal.ofReal (w y) * ENNReal.ofReal ((w y)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (hwpos y).le, mul_inv_cancel₀ (hwpos y).ne', ENNReal.ofReal_one]
  apply eLpNorm_weighted_integral_domination hF₀ hw.ennreal_ofReal hT hp
  · intro y
    change eLpNorm ((w y)⁻¹ • fun x => F (x, y)) (ENNReal.ofReal p) μ ≤ B
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr (hwpos y).le)]
    calc
      _ ≤ ENNReal.ofReal ((w y)⁻¹) * (ENNReal.ofReal (w y) * B) :=
        mul_le_mul' le_rfl (hbound y)
      _ = B := by rw [← mul_assoc, mul_comm (ENNReal.ofReal ((w y)⁻¹)), hid, one_mul]
  · intro x
    apply (hdom x).trans_eq
    apply lintegral_congr
    intro y
    simp only [F₀, enorm_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr (hwpos y).le)]
    rw [← mul_assoc, hid, one_mul]

end OAI.Analysis.Fourier.SquareFunction
