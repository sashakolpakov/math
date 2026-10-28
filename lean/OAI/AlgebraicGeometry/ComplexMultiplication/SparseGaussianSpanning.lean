import OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums
import OAI.AlgebraicGeometry.ComplexMultiplication.LatticeGaussian
import Mathlib.Analysis.Complex.Basic

/-! # Sparse Gaussian Spanning -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SparseGaussianSpanning.CM

noncomputable section

/-!
# Sparse Gaussian sums span projected linear terms

The norm estimate needed for a theta gradient is explicit: its scalar
weight has a positive Gaussian bound and its vector factor is a continuous
linear map of the real position space. The resulting lattice family is
absolutely summable. Sparse positive-degree cosets isolate its terms.

This establishes the analytic spanning deduction once the actual theta
gradient and its projection have been identified with this family. It
does not assert the manuscript's transformation or holomorphicity claims.
-/

open Filter _root_.Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [CompleteSpace W]

/-- A Gaussian-weighted linear position factor, the form of a projected
first Taylor coefficient at a fixed period point. -/
def weightedLatticeLinearTerm (χ : V → ℂ) (P : V →L[ℝ] W) (x : L) : W :=
  χ x • P x

omit [CompleteSpace W] in
theorem weightedLatticeLinearTerm_norm_summable (χ : V → ℂ) (P : V →L[ℝ] W)
    (a b : ℝ) (ha : 0 < a)
    (hχ : ∀ x : L, ‖χ x‖ ≤ Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖)) :
    Summable (fun x => ‖weightedLatticeLinearTerm L χ P x‖) := by
  apply ((LatticeGaussian.CM.lattice_gaussian_poly_summable L a b ha 1).mul_left ‖P‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro x
  change ‖χ x • P x‖ ≤ ‖P‖ * (‖x‖ ^ 1 * Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖))
  rw [norm_smul, pow_one]
  calc
    ‖χ x‖ * ‖P x‖ ≤ Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖) * (‖P‖ * ‖(x : V)‖) :=
      mul_le_mul (hχ x) (P.le_opNorm x) (norm_nonneg _) (Real.exp_pos _).le
    _ = ‖P‖ * (‖x‖ * Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖)) := by
      change _ = ‖P‖ * (‖(x : V)‖ * _)
      ring

/-- Every projected position vector with nonzero scalar weight belongs to
the span of genuine sparse-coset sums of the weighted family. -/
theorem projected_mem_span_sparseGaussianSums [FiniteDimensional ℂ W]
    (χ : V → ℂ) (P : V →L[ℝ] W) (a b : ℝ) (ha : 0 < a)
    (hχ : ∀ x : L, ‖χ x‖ ≤ Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖))
    (x : L) (hx : χ x ≠ 0) :
    P x ∈ Submodule.span ℂ
      (Set.range (SparseLatticeSums.CM.sparseLatticeSum L (weightedLatticeLinearTerm L χ P) x)) := by
  apply (Submodule.smul_mem_iff _ hx).mp
  exact SparseLatticeSums.CM.mem_span_sparseLatticeSums L (weightedLatticeLinearTerm L χ P)
    (weightedLatticeLinearTerm_norm_summable L χ P a b ha hχ) x

/-- A nonzero projected position vector produces nonzero sums in all
sufficiently sparse positive degrees. -/
theorem sparseGaussianSum_eventually_ne_zero
    (χ : V → ℂ) (P : V →L[ℝ] W) (a b : ℝ) (ha : 0 < a)
    (hχ : ∀ x : L, ‖χ x‖ ≤ Real.exp (-a * ‖x‖ ^ 2 + b * ‖x‖))
    (x : L) (hx : χ x ≠ 0) (hP : P x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, SparseLatticeSums.CM.sparseLatticeSum L (weightedLatticeLinearTerm L χ P) x n ≠ 0 :=
  SparseLatticeSums.CM.sparseLatticeSum_eventually_ne_zero L (weightedLatticeLinearTerm L χ P)
    (weightedLatticeLinearTerm_norm_summable L χ P a b ha hχ) x (smul_ne_zero hx hP)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SparseGaussianSpanning.CM
