import OAI.Analysis.Fourier.BochnerRiesz.DualityNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- Testing against Schwartz functions already detects the `Lᵖ` norm.
The integrability hypothesis is useful for smooth multiplier approximants. -/
theorem eLpNorm_le_of_schwartz_pairing {n : ℕ} {p : ℝ} (hp : 1 < p)
    {f : Space n → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) {A : ℝ≥0∞}
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      ‖∫ x, g x * f x‖ₑ ≤ A * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ A := by
  by_cases hAt : A = ⊤
  · simp [hAt]
  have hpq : p.HolderConjugate (p / (p - 1)) := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have := hpq.symm.ennrealOfReal
  have hq1 : 1 ≤ ENNReal.ofReal (p / (p - 1)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (Real.holderConjugate_iff.mp hpq.symm).1.le
  apply eLpNorm_le_of_integral_mul_bound volume hp hf
  intro g hg
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨η, hη, hηbound⟩ := OAI.Analysis.Fourier.SquareFunction.exists_pos_mul_ofReal_le
    (C := A + eLpNorm f (ENNReal.ofReal p) volume) (ENNReal.add_ne_top.mpr ⟨hAt, hf.ne⟩) hε
  obtain ⟨u, hu⟩ := OAI.Analysis.Fourier.SquareFunction.exists_schwartz_eLpNorm_sub_le hq1 ENNReal.ofReal_ne_top hg hη
  have hnormu : eLpNorm u (ENNReal.ofReal (p / (p - 1))) volume ≤
      eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume + ENNReal.ofReal η := by
    have he : (u : Space n → ℂ) = g - (g - (u : Space n → ℂ)) := by ext x; simp
    rw [he]
    exact (eLpNorm_sub_le hq1).trans (add_le_add le_rfl hu)
  have hui : Integrable (fun x ↦ u x * f x) :=
    memLp_one_iff_integrable.mp ((u.memLp (ENNReal.ofReal (p / (p - 1))) volume).fun_mul hf)
  have hri : Integrable (fun x ↦ (g - (u : Space n → ℂ)) x * f x) :=
    memLp_one_iff_integrable.mp ((hg.sub (u.memLp (ENNReal.ofReal (p / (p - 1))) volume)).fun_mul hf)
  have he : (∫ x, g x * f x) =
      (∫ x, u x * f x) + ∫ x, (g - (u : Space n → ℂ)) x * f x := by
    rw [← integral_add hui hri]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  calc
    _ = ‖(∫ x, u x * f x) + ∫ x, (g - (u : Space n → ℂ)) x * f x‖ₑ := congrArg (fun z : ℂ ↦ ‖z‖ₑ) he
    _ ≤ ‖∫ x, u x * f x‖ₑ + ‖∫ x, (g - (u : Space n → ℂ)) x * f x‖ₑ := enorm_add_le _ _
    _ ≤ A * eLpNorm u (ENNReal.ofReal (p / (p - 1))) volume +
        eLpNorm (g - (u : Space n → ℂ)) (ENNReal.ofReal (p / (p - 1))) volume *
          eLpNorm f (ENNReal.ofReal p) volume :=
      add_le_add (hbound u) (enorm_integral_mul_le_eLpNorm volume
        (hg.aestronglyMeasurable.sub u.continuous.aestronglyMeasurable) hf.aestronglyMeasurable hpq.symm)
    _ ≤ A * (eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume + ENNReal.ofReal η) +
        ENNReal.ofReal η * eLpNorm f (ENNReal.ofReal p) volume :=
      add_le_add (mul_le_mul' le_rfl hnormu) (mul_le_mul' hu le_rfl)
    _ = A * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume +
        (A + eLpNorm f (ENNReal.ofReal p) volume) * ENNReal.ofReal η := by ring
    _ ≤ _ := add_le_add le_rfl hηbound

end OAI.Analysis.Fourier.BochnerRiesz
