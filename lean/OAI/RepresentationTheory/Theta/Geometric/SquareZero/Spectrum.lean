import OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearDetection
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Prime

/-! # Spectrum -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Spectrum

noncomputable section

/-! The split square-zero extension of the complex field by any complex
vector space has exactly one underlying scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M]

theorem squareZero_prime_mem (p : PrimeSpectrum (TrivSqZeroExt ℂ M)) (x : TrivSqZeroExt ℂ M) :
    x ∈ p.asIdeal ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra hn
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hn)
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hx hu)
  · intro hx
    have hsq : x ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext
      · simp [TrivSqZeroExt.fst_mul, hx]
      · simp [TrivSqZeroExt.snd_mul, hx]
    exact p.isPrime.mem_of_pow_mem 2 (hsq.symm ▸ p.asIdeal.zero_mem)

theorem squareZero_primeSpectrum_subsingleton : Subsingleton (PrimeSpectrum (TrivSqZeroExt ℂ M)) := by
  refine ⟨fun p q => ?_⟩
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro x
  exact (squareZero_prime_mem p x).trans (squareZero_prime_mem q x).symm

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Spectrum
