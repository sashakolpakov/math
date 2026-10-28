import OAI.MeasureTheory.Kakeya.Randomization

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- A spherical restriction estimate controls the square sum of the actual
modulated cap extensions. Randomization removes cross terms, while disjoint
caps make every signed input have the same exact norm. -/
theorem restriction_implies_packet_square_estimate
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {r q : ℝ} (hr : 1 < r) (hq : 2 ≤ q)
    (hcrit : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q)
    (hdiag : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal r) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ),
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
        (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)) volume ∧
      (∫ y, (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
        (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)) ≤
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
  obtain ⟨C, hC, hbound⟩ := hR n hn (ENNReal.ofReal r) (ENNReal.one_lt_ofReal.mpr hr)
    q hcrit hdiag
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x c hsep
  let g : Fin m → Space n → ℂ := fun i ω ↦ c i * capPacket δ (v i) (x i) ω
  let z : Fin m → Space n → ℂ := fun i y ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) y
  let f : (Fin m → Bool) → Space n → ℂ := fun ε ω ↦ signedSum (fun i ↦ g i ω) ε
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by linarith
  have hg (i : Fin m) : Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (integrable_capPacket δ (v i) (x i)).const_mul (c i)
  have hf (ε : Fin m → Bool) : MemLp (f ε) (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_signedPackets hδ v x c ε hsep hr0
  have hE (ε : Fin m → Bool) : OAI.Analysis.Fourier.Restriction.sphericalExtension (f ε) =
      fun y ↦ signedSum (fun i ↦ z i y) ε := by
    funext y
    exact sphericalExtension_signedSum g hg ε y
  have hi (ε : Fin m → Bool) :
      Integrable (fun y ↦ ‖signedSum (fun i ↦ z i y) ε‖ ^ q) volume := by
    have h := (hbound (f ε) (hf ε)).1.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq0.le, hE ε] using h
  have hpow (ε : Fin m → Bool) :
      (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) ≤
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
    have h := OAI.Analysis.Fourier.Restriction.integral_norm_rpow_le_of_eLpNorm_le hr0 hq0 hC.le (hf ε)
      (hbound (f ε) (hf ε)).1 (hbound (f ε) (hf ε)).2
    rw [hE ε] at h
    change (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) ≤
      C ^ q * (∫ ω, ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ r
        ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ (q / r) at h
    rw [integral_norm_signedPackets_rpow hδ v x c ε hsep hr0] at h
    exact h
  have hJ := integral_sign_randomization_lower z hq
    (fun i ↦ (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension (hg i)).aestronglyMeasurable) hi
  refine ⟨hJ.1, hJ.2.trans ?_⟩
  calc
    (∑ ε : Fin m → Bool, ∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) / (2 : ℝ) ^ m ≤
      (∑ _ε : Fin m → Bool,
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) /
          (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ ↦ hpow ε) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

end OAI.MeasureTheory.Kakeya
