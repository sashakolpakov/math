import OAI.AlgebraicGeometry.ComplexMultiplication.SiegelThetaSeries
import OAI.AlgebraicGeometry.ComplexMultiplication.SparseGaussianSpanning

/-! # Siegel Theta Spanning -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SiegelThetaSpanning.CM.SiegelPhase

noncomputable section

/-!
# Spanning by actual first derivatives of sparse theta series

This connects the Gaussian isolation argument to actual derivatives of
the explicit theta exponential series. All sparse supports have positive
integer multiplier. The phase is fixed; automorphic transformation and
projection onto the ball cotangent bundle remain separate obligations.
-/

open scoped Classical
open Filter _root_.Topology

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  (Z : CMSiegelPhase.CM.SiegelPhase V) (P : V →L[ℝ] (U →L[ℂ] ℂ))
  (L : Submodule ℤ V) [DiscreteTopology L]

/-- The actual gradient in the Jacobi variable for the positive-degree
sparse input supported on `a + (n + 1)L`. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient (a : L) (n : ℕ) : U →L[ℂ] ℂ :=
  fderiv ℂ (Z.thetaSeriesOn P L {x | SparseLatticeSums.CM.SparseLatticeCoset L n a x}) 0

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient_eq (a : L) (n : ℕ) :
    Z.sparseThetaGradient P L a n =
      SparseLatticeSums.CM.sparseLatticeSum L
        (SparseGaussianSpanning.CM.weightedLatticeLinearTerm L Z.gaussianWeight ((2 * (Real.pi : ℂ) * Complex.I) • P)) a n := by
  rw [CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient, Z.fderiv_thetaSeriesOn]
  unfold CMSiegelPhase.CM.SiegelPhase.thetaSeriesOnDerivative SparseLatticeSums.CM.sparseLatticeSum
  apply tsum_congr
  intro x
  simp only [CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative, Set.mem_ofPred_eq, CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative,
    Z.thetaTerm_zero, SparseGaussianSpanning.CM.weightedLatticeLinearTerm, smul_apply]

private theorem theta_gradient_factor_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

/-- The actual gradients converge to the nonzero Gaussian multiple of the
chosen position covector as the positive coset multiplier tends to infinity. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient_tendsto (x : L) :
    Tendsto (Z.sparseThetaGradient P L x) atTop
      (𝓝 (Z.gaussianWeight x • ((2 * (Real.pi : ℂ) * Complex.I) • P x))) := by
  have hw : ∀ l : L, ‖Z.gaussianWeight l‖ ≤
      Real.exp (-(Real.pi * Z.lowerBound) * ‖l‖ ^ 2 + 0 * ‖l‖) := by
    intro l
    simpa only [zero_mul, add_zero] using! Z.gaussianWeight_norm_le l
  have hs := SparseGaussianSpanning.CM.weightedLatticeLinearTerm_norm_summable L Z.gaussianWeight
    ((2 * (Real.pi : ℂ) * Complex.I) • P) (Real.pi * Z.lowerBound) 0
    (mul_pos Real.pi_pos Z.lowerBound_pos) hw
  have heq : Z.sparseThetaGradient P L x = SparseLatticeSums.CM.sparseLatticeSum L
      (SparseGaussianSpanning.CM.weightedLatticeLinearTerm L Z.gaussianWeight ((2 * (Real.pi : ℂ) * Complex.I) • P)) x :=
    funext (Z.sparseThetaGradient_eq P L x)
  rw [heq]
  exact SparseLatticeSums.CM.sparseLatticeSum_tendsto L _ hs x

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.pairing_mem_span_sparseThetaGradients [FiniteDimensional ℂ U] (x : L) :
    P x ∈ Submodule.span ℂ (Set.range (Z.sparseThetaGradient P L x)) := by
  have hw : ∀ l : L, ‖Z.gaussianWeight l‖ ≤
      Real.exp (-(Real.pi * Z.lowerBound) * ‖l‖ ^ 2 + 0 * ‖l‖) := by
    intro l
    simpa only [zero_mul, add_zero] using! Z.gaussianWeight_norm_le l
  have h := SparseGaussianSpanning.CM.projected_mem_span_sparseGaussianSums L Z.gaussianWeight
    ((2 * (Real.pi : ℂ) * Complex.I) • P) (Real.pi * Z.lowerBound) 0
    (mul_pos Real.pi_pos Z.lowerBound_pos) hw x (Z.gaussianWeight_ne_zero x)
  have heq : Z.sparseThetaGradient P L x = SparseLatticeSums.CM.sparseLatticeSum L
      (SparseGaussianSpanning.CM.weightedLatticeLinearTerm L Z.gaussianWeight ((2 * (Real.pi : ℂ) * Complex.I) • P)) x :=
    funext (Z.sparseThetaGradient_eq P L x)
  rw [← heq] at h
  exact (Submodule.smul_mem_iff _ theta_gradient_factor_ne_zero).mp h

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient_eventually_ne_zero (x : L) (hx : P x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, Z.sparseThetaGradient P L x n ≠ 0 := by
  have hw : ∀ l : L, ‖Z.gaussianWeight l‖ ≤
      Real.exp (-(Real.pi * Z.lowerBound) * ‖l‖ ^ 2 + 0 * ‖l‖) := by
    intro l
    simpa only [zero_mul, add_zero] using! Z.gaussianWeight_norm_le l
  have h := SparseGaussianSpanning.CM.sparseGaussianSum_eventually_ne_zero L Z.gaussianWeight
    ((2 * (Real.pi : ℂ) * Complex.I) • P) (Real.pi * Z.lowerBound) 0
    (mul_pos Real.pi_pos Z.lowerBound_pos) hw x (Z.gaussianWeight_ne_zero x)
    (smul_ne_zero theta_gradient_factor_ne_zero hx)
  filter_upwards [h] with n hn
  rwa [Z.sparseThetaGradient_eq]

/-- If projected lattice positions span the cotangent space, actual sparse
theta gradients span it as well. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.span_sparseThetaGradients_eq_top [FiniteDimensional ℂ U]
    (hP : Submodule.span ℂ (Set.range (fun x : L => P x)) = ⊤) :
    Submodule.span ℂ (Set.range (fun an : L × ℕ => Z.sparseThetaGradient P L an.1 an.2)) = ⊤ := by
  apply top_unique
  rw [← hP]
  apply Submodule.span_le.mpr
  rintro y ⟨x, rfl⟩
  apply (Submodule.span_mono (show Set.range (Z.sparseThetaGradient P L x) ⊆
      Set.range (fun an : L × ℕ => Z.sparseThetaGradient P L an.1 an.2) from ?_))
    (Z.pairing_mem_span_sparseThetaGradients P L x)
  rintro _ ⟨n, rfl⟩
  exact ⟨(x, n), rfl⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SiegelThetaSpanning.CM.SiegelPhase
