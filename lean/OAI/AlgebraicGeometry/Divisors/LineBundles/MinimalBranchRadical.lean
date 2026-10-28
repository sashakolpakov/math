import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImageAnnihilator
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! # Minimal Branch Radical -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchRadical.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the radical of the actual branch-image annihilator

At a minimal prime P over I, every prime over the localized ideal is
the maximal ideal of R_P. Contracting the radical therefore gives P.
-/

variable {R : Type*} [CommRing R]

theorem minimalPrime_localized_radical (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization P.primeCompl))).radical =
      IsLocalRing.maximalIdeal (Localization P.primeCompl) := by
  have hle : I.map (algebraMap R (Localization P.primeCompl)) ≤
      IsLocalRing.maximalIdeal (Localization P.primeCompl) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hP.le
  apply le_antisymm
  · exact (Ideal.radical_mono hle).trans_eq
      (inferInstance : (IsLocalRing.maximalIdeal (Localization P.primeCompl)).IsPrime).radical
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.radical_eq_sInf]
    apply le_sInf
    rintro J ⟨hIJ, hJ⟩
    obtain ⟨hJR, hJP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization P.primeCompl) P) ⟨J, hJ⟩).2
    rw [Ideal.map_le_iff_le_comap] at hIJ ⊢
    exact hP.2 ⟨hJR, hIJ⟩ hJP

theorem minimalPrime_branch_annihilator_radical (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) :
    (Module.annihilator R (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I))).radical = P := by
  rw [LocalizationImageAnnihilator.BundleCycles.localizationImage_quotient_annihilator]
  change ((I.map (algebraMap R (Localization P.primeCompl))).comap
    (algebraMap R (Localization P.primeCompl))).radical = P
  rw [← Ideal.comap_radical, minimalPrime_localized_radical I P hP]
  exact Localization.AtPrime.under_maximalIdeal

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchRadical.BundleCycles
