import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

/-! # Sparse Lattice Sums -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM

noncomputable section

/-!
# Isolating a lattice term by increasingly sparse cosets

For an absolutely summable lattice-valued family, sums over
`a + (n + 1) L` converge to the single term at `a`. No degree-zero
coset is admitted. In a finite-dimensional target, the sparse-coset
sums therefore span every individual term. This is the analytic
isolation step in the manuscript's projected-gradient spanning argument;
the theta transformation and projection still need to be connected to it.
-/

open scoped Classical
open Filter _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (L : Submodule ℤ V) [DiscreteTopology L]

/-- A positive-integer sparse coset of the actual lattice. -/
def SparseLatticeCoset (n : ℕ) (a x : L) : Prop := ∃ l : L, x = a + (n + 1) • l

omit [NormedSpace ℝ V] [DiscreteTopology L] in
theorem sparseLatticeCoset_center (n : ℕ) (a : L) : SparseLatticeCoset L n a a :=
  ⟨0, by simp⟩

/-- Every other lattice point is eventually excluded from the sparse coset. -/
theorem eventually_not_sparseLatticeCoset (a x : L) (hxa : x ≠ a) :
    ∀ᶠ n : ℕ in atTop, ¬ SparseLatticeCoset L n a x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_discrete ({(0 : L)} : Set L)) 0 (by simp)
  have hsmall : ∀ l : L, ‖l‖ < δ → l = 0 := by
    intro l hl
    exact hball (by simpa only [Metric.mem_ball, dist_zero_right] using hl)
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x - a‖ / δ)
  have hN' : ‖x - a‖ < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  rintro ⟨l, hl⟩
  have hl0 : l ≠ 0 := by
    intro hz
    apply hxa
    simpa only [hz, smul_zero, add_zero] using hl
  have hlbound : δ ≤ ‖l‖ := le_of_not_gt (fun h => hl0 (hsmall l h))
  have hsize : ‖x - a‖ = ((n + 1 : ℕ) : ℝ) * ‖l‖ := by
    have heq := congrArg (fun y : L => (y : V)) hl
    change (x : V) = (a : V) + (n + 1) • (l : V) at heq
    change ‖(x : V) - (a : V)‖ = ((n + 1 : ℕ) : ℝ) * ‖(l : V)‖
    rw [heq, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  have hn' : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (hn.trans (Nat.le_succ n))
  have hlarge := mul_le_mul hn' hlbound hδ.le (Nat.cast_nonneg (n + 1))
  rw [← hsize] at hlarge
  exact (not_le_of_gt hN') hlarge

variable {W : Type*} [NormedAddCommGroup W] [CompleteSpace W]

/-- A coset-supported sum; the multiplier is always strictly positive. -/
def sparseLatticeSum (f : L → W) (a : L) (n : ℕ) : W :=
  ∑' x : L, if SparseLatticeCoset L n a x then f x else 0

theorem sparseLatticeSum_tendsto (f : L → W) (hf : Summable (fun x => ‖f x‖)) (a : L) :
    Tendsto (sparseLatticeSum L f a) atTop (𝓝 (f a)) := by
  have hpoint : ∀ x : L, Tendsto
      (fun n : ℕ => if SparseLatticeCoset L n a x then f x else 0)
      atTop (𝓝 (if x = a then f a else 0)) := by
    intro x
    by_cases hxa : x = a
    · subst x
      simpa only [sparseLatticeCoset_center, ite_true] using
        (tendsto_const_nhds (x := f a) : Tendsto (fun _ : ℕ => f a) atTop (𝓝 (f a)))
    · rw [ite_eq_right hxa]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_not_sparseLatticeCoset L a x hxa] with n hn
      simp only [ite_eq_right hn]
  have h := tendsto_tsum_of_dominated_convergence hf hpoint
    (show ∀ᶠ n : ℕ in atTop, ∀ x : L,
      ‖if SparseLatticeCoset L n a x then f x else 0‖ ≤ ‖f x‖ from by
      exact Eventually.of_forall (fun n x => by split_ifs <;> simp))
  simpa only [sparseLatticeSum, tsum_ite_eq] using! h

/-- A nonzero isolated term gives nonzero coset sums in sufficiently
sparse positive degrees. -/
theorem sparseLatticeSum_eventually_ne_zero (f : L → W)
    (hf : Summable (fun x => ‖f x‖)) (a : L) (ha : f a ≠ 0) :
    ∀ᶠ n : ℕ in atTop, sparseLatticeSum L f a n ≠ 0 :=
  (sparseLatticeSum_tendsto L f hf a).eventually_ne ha

/-- Finite-dimensional closedness upgrades the limit to membership in the
span of the actual positive-degree coset sums. -/
theorem mem_span_sparseLatticeSums [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (f : L → W) (hf : Summable (fun x => ‖f x‖)) (a : L) :
    f a ∈ Submodule.span ℂ (Set.range (sparseLatticeSum L f a)) := by
  apply (Submodule.closed_of_finiteDimensional
    (Submodule.span ℂ (Set.range (sparseLatticeSum L f a)))).mem_of_tendsto
      (sparseLatticeSum_tendsto L f hf a)
  exact Eventually.of_forall (fun n => Submodule.subset_span ⟨n, rfl⟩)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM
