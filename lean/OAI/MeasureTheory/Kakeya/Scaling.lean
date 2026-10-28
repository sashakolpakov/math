import OAI.MeasureTheory.Kakeya.CapReduction
import OAI.Analysis.Fourier.Restriction.Geometry

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem cap_coefficient_scale {δ C L U q a b : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U) (hq : 0 < q) :
    (δ ^ a * C ^ (2 * q) * (U * δ ^ b) * (2 / (L * δ ^ b)) ^ (2 * q)) ^ (1 / q) =
      (C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q) *
        δ ^ ((a + b) / q - 2 * b) := by
  have hdiv : 2 / (L * δ ^ b) = (2 / L) / δ ^ b := by ring
  have hinner : δ ^ a * C ^ (2 * q) * (U * δ ^ b) * (2 / (L * δ ^ b)) ^ (2 * q) =
      (C ^ (2 * q) * U * (2 / L) ^ (2 * q)) * δ ^ (a + b - b * (2 * q)) := by
    rw [hdiv, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ.le]
    rw [Real.rpow_sub hδ, Real.rpow_add hδ]
    ring
  rw [hinner, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ.le]
  congr 2
  field_simp

/-- The finite tube-integral estimate with its sharp scale power, conditional
only on spherical restriction. All cap-size geometry has been discharged. -/
theorem restriction_implies_finite_tube_integrals
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤
        A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) *
          (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_finite_tube_integrals_with_cap_bounds hR n hn hpq hpn
  obtain ⟨L, U, hL, hU, hcap⟩ := OAI.Analysis.Fourier.Restriction.packetCap_real_comparable (n := n) (by omega)
  refine ⟨(C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q), by positivity, ?_⟩
  intro m δ hδ hδone v x hv hsep f hf
  have h := hbound m δ hδ v x hv hsep (L * δ ^ (n - 1)) (U * δ ^ (n - 1))
    (by positivity) (by positivity)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).1)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).2) f hf
  have hdim : (δ ^ 2) ^ n = δ ^ (2 * (n : ℝ)) := by
    rw [← pow_mul]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Real.rpow_natCast δ (2 * n)).symm
  have hd : δ ^ (n - 1) = δ ^ ((n - 1 : ℕ) : ℝ) := (Real.rpow_natCast δ (n - 1)).symm
  rw [hdim, hd, cap_coefficient_scale hδ hC.le hL hU.le hpq.symm.pos] at h
  exact h

end OAI.MeasureTheory.Kakeya
