import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import Mathlib.RingTheory.Ideal.Prime

/-! # Number Spectrum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum

noncomputable section

/-! The spectrum of the actual dual-number ring over a field is a
single point; its reduction map is surjective on scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type*} [Field k]

theorem dualNumber_prime_mem (p : PrimeSpectrum (DualNumber k)) (z : DualNumber k) :
    z ∈ p.asIdeal ↔ z.fst = 0 := by
  constructor
  · intro hz
    by_contra h
    have hu : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hz hu)
  · intro hz
    have hsq : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext
      · change z.fst * z.fst = 0
        rw [hz, zero_mul]
      · rw [DualNumber.snd_mul, hz, zero_mul, mul_zero, add_zero]
        rfl
    exact p.isPrime.mem_of_pow_mem 2 (hsq.symm ▸ p.asIdeal.zero_mem)

theorem dualNumber_primeSpectrum_subsingleton : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  refine ⟨fun p q => ?_⟩
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro z
  exact (dualNumber_prime_mem p z).trans (dualNumber_prime_mem q z).symm

theorem dualNumberOrigin_surjective : Surjective (LieRanks.dualNumberOrigin k).left := by
  let : Subsingleton (LieRanks.dualNumberTest k).left := dualNumber_primeSpectrum_subsingleton
  let : Nonempty ((Over.mk (𝟙 (Spec (.of k)))).left) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact ⟨Function.surjective_to_subsingleton _⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberSpectrum
