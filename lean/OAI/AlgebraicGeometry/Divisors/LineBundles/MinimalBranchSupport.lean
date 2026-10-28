import OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchRadical
import Mathlib.RingTheory.Support

/-! # Minimal Branch Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchSupport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: exact support of the actual minimal-branch image
-/

variable {R : Type*} [CommRing R]

theorem minimalPrime_branch_support_iff (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) (q : PrimeSpectrum R) :
    q ∈ Module.support R (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I)) ↔ P ≤ q.asIdeal := by
  rw [Module.mem_support_iff_of_finite, ← q.isPrime.radical_le_iff,
    MinimalBranchRadical.BundleCycles.minimalPrime_branch_annihilator_radical I P hP]

theorem minimalPrime_branch_localization_zero (I P : Ideal R) [P.IsPrime]
    (hP : P ∈ I.minimalPrimes) (q : PrimeSpectrum R) (hpq : ¬ P ≤ q.asIdeal) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl
      (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I))) :=
  Module.notMem_support_iff.mp (fun hq => hpq ((minimalPrime_branch_support_iff I P hP q).mp hq))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchSupport.BundleCycles
