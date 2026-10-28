import OAI.Analysis.PDE.Weak.Boundary.H1Translation
import OAI.Analysis.PDE.Weak.Boundary.Weak.Test
import OAI.Analysis.PDE.Weak.Elliptic.Adjoint
import OAI.Analysis.PDE.Weak.Elliptic.Energy

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The discrete integration-by-parts identity for completed, rather than
only smooth, admissible test functions. -/
theorem WeakDivergenceEquation.shifted_h1Zero_test
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    {f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hweak : WeakDivergenceEquation Ω H f)
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ) (q : H1Pair m)
    (hq : differenceH1Pair v (-h) q ∈ H1Zero Ω) :
    inner ℝ (differenceQuotientL2 volume v h H) q.2 =
      -inner ℝ f (differenceQuotientL2 volume v (-h) q.1) := by
  have he := hweak.h1Zero_test hq
  change inner ℝ H (differenceQuotientL2 volume v (-h) q.2) =
    inner ℝ f (differenceQuotientL2 volume v (-h) q.1) at he
  rw [inner_differenceQuotientL2, he]

/-- The forcing term is uniformly controlled by the gradient of the
completed test, with no reciprocal-step loss. -/
theorem WeakDivergenceEquation.shifted_h1Zero_test_bound
    {Ω Ω' : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    {H : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    {f : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hweak : WeakDivergenceEquation Ω H f)
    (j : Fin (m + 1)) {h : ℝ} (hh : h ≠ 0) {q : H1Pair m}
    (hq : q ∈ H1Zero Ω')
    (hback : differenceH1Pair (Pi.single j 1) (-h) q ∈ H1Zero Ω) :
    |inner ℝ (differenceQuotientL2 volume (Pi.single j 1) h H) q.2| ≤
      ‖f‖ * ‖q.2‖ := by
  rw [hweak.shifted_h1Zero_test (Pi.single j 1) h q hback, abs_neg]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (OAI.Analysis.PDE.Weak.H1Zero.difference_bound hq j (neg_ne_zero.mpr hh)) (norm_nonneg _))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coercive algebra after the actual cutoff test is inserted.  The
commutator and the forcing are measured explicitly, not assumed small. -/
theorem coercive_cutoff_energy_bound (A : E →L[ℝ] E) (P U Q R : E)
    {lam Λ F : ℝ} (hlam : 0 < lam) (_ : 0 ≤ Λ) (hF : 0 ≤ F)
    (hA : ‖A‖ ≤ Λ)
    (hell : lam * ‖P‖ ^ 2 ≤ inner ℝ (A P) P)
    (hQ : ‖Q‖ ≤ ‖P‖ + 2 * ‖U‖)
    (heq : |inner ℝ (A P) (P + (2 : ℝ) • U) + inner ℝ R Q| ≤ F * ‖Q‖) :
    ‖P‖ ^ 2 ≤
      ((F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 / lam +
        4 * (F + ‖R‖) * ‖U‖) / lam := by
  have hcross : |inner ℝ (A P) U| ≤ Λ * ‖P‖ * ‖U‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((A.le_opNorm P).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
      (norm_nonneg _))
  have hr := abs_real_inner_le_norm R Q
  have he := (le_abs_self _).trans heq
  have hl := neg_abs_le (inner ℝ R Q)
  have hc := neg_abs_le (inner ℝ (A P) U)
  have hqmul := mul_le_mul_of_nonneg_left hQ (show 0 ≤ F + ‖R‖ by positivity)
  have hmain : lam * ‖P‖ ^ 2 ≤
      (F + ‖R‖ + 2 * Λ * ‖U‖) * ‖P‖ + 2 * (F + ‖R‖) * ‖U‖ := by
    simp only [inner_add_right, real_inner_smul_right] at he
    nlinarith
  have hy := weightedYoung hlam ‖P‖ (F + ‖R‖ + 2 * Λ * ‖U‖)
  apply (le_div_iff₀ hlam).mpr
  have hi : (F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 / lam =
      lam⁻¹ * (F + ‖R‖ + 2 * Λ * ‖U‖) ^ 2 := by ring
  rw [hi]
  nlinarith

end OAI.Analysis.PDE.Weak
