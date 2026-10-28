import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Perfect Quotient -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.PerfectQuotient

noncomputable section

/-! # Reduced quotients of perfect rings are perfect -/

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] [PerfectRing R p]
  (I : Ideal R) [CharP (R ⧸ I) p] [IsReduced (R ⧸ I)]

theorem perfectRing : PerfectRing (R ⧸ I) p := by
  apply PerfectRing.ofSurjective (R ⧸ I) p
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk I ((frobeniusEquiv R p).symm r), ?_⟩
  change (Ideal.Quotient.mk I ((frobeniusEquiv R p).symm r)) ^ p = Ideal.Quotient.mk I r
  rw [← map_pow, frobeniusEquiv_symm_pow_p]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.PerfectQuotient
