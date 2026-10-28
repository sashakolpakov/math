import OAI.Analysis.Theta.GaussianConvergenceGaussian
import OAI.Analysis.Theta.Sparse

/-! # Gaussian Convergence -/

namespace OAI.Analysis.Theta.GaussianConvergence

noncomputable section

/-!
GaussianConvergence: Gaussian convergence of theta derivatives.
The proof keeps the statement's fixed discrete lattice, bounded coefficients,
joint compact parameter sets, and cosets `a + (n + 1)L`. The supporting
parameter abbreviation unfolds `Matrix` solely for norm-instance synthesis.
No statement stub is imported.
-/

open scoped Classical BigOperators _root_.Topology
  BoundedContinuousFunction Matrix.Norms.Elementwise
open Filter

namespace Construction
variable {ι : Type*} [Fintype ι]

/--
Uniform Gaussian domination through any finite derivative order,
smooth dependence, termwise differentiation, and uniform isolation
of a lattice term by sparse cosets.
-/
theorem gaussian_theta_derivatives
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (φ : L →ᵇ ℂ)
    (K : Set (GaussianConvergenceGaussian.Construction.ThetaParameters ι))
    (hK : IsCompact K)
    (hKpos : ∀ p ∈ K, p.1 ∈ RepresentationTheory.Theta.Definitions.siegelDomain)
    (m : ℕ) :
    let Θ : GaussianConvergenceGaussian.Construction.ThetaParameters ι → ℂ :=
      fun p => RepresentationTheory.Theta.Definitions.theta L φ p.1 p.2
    -- A common summable Gaussian majorant for orders 0 through m.
    (∃ C c b : ℝ,
      let M : L → ℝ := fun x =>
        C * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) *
          Real.exp
            (-c * ‖(x : ι → ℝ)‖ ^ 2 +
              b * ‖(x : ι → ℝ)‖)
      0 < C ∧ 0 < c ∧ 0 ≤ b ∧ Summable M ∧
        ∀ k ≤ m, ∀ x : L, ∀ p ∈ K,
          ‖iteratedFDeriv ℂ k (GaussianConvergenceGaussian.Construction.thetaSummand L φ x) p‖ ≤ M x) ∧
    -- Smoothness in the ambient complex parameter space.
    (∀ p ∈ K, ContDiffAt ℂ ⊤ Θ p) ∧
    -- The differentiated series sums to the actual derivative.
    (∀ k ≤ m, ∀ p ∈ K,
      HasSum
        (fun x : L =>
          iteratedFDeriv ℂ k (GaussianConvergenceGaussian.Construction.thetaSummand L φ x) p)
        (iteratedFDeriv ℂ k Θ p)) ∧
    -- Cosets a + (n + 1)L isolate the term at a, uniformly on K.
    (∀ k ≤ m, ∀ a : L,
      TendstoUniformlyOn
        (fun n p =>
          AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L
            (fun x =>
              iteratedFDeriv ℂ k (GaussianConvergenceGaussian.Construction.thetaSummand L φ x) p)
            a n)
        (fun p => iteratedFDeriv ℂ k (GaussianConvergenceGaussian.Construction.thetaSummand L φ a) p)
        atTop K) := by
  dsimp only
  obtain ⟨c, hc, hquad⟩ := GaussianConvergenceGaussian.Construction.compact_quadratic_lower_bound K hK hKpos
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun p : GaussianConvergenceGaussian.Construction.ThetaParameters ι => p.2) continuous_snd.continuousOn
  obtain ⟨C, d, b, hC, hd, hb, hM, hbound⟩ :=
    GaussianConvergenceGaussian.Construction.gaussian_majorant_on_set L φ K c (max R 0) hc (le_max_right _ _)
      hquad (fun p hp => (hR p hp).trans (le_max_left _ _)) m
  refine ⟨⟨C, d, b, hC, hd, hb, hM, hbound⟩, ?_, ?_, ?_⟩
  · intro p hp
    let Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι := ⟨p.1, (hKpos p hp).1, (hKpos p hp).2⟩
    simpa using! (RepresentationTheory.Theta.Analytic.theta_joint_analytic L φ Z p.2).contDiffAt
  · intro k _ p hp
    exact GaussianConvergenceGaussian.Construction.theta_derivative_hasSum L φ p (hKpos p hp) k
  · intro k hk a
    apply Sparse.GaussianConvergenceConstruction.sparse_uniform_of_summable_bound L K
      (fun x p => iteratedFDeriv ℂ k (GaussianConvergenceGaussian.Construction.thetaSummand L φ x) p)
      (fun x => ((GaussianConvergenceGaussian.Construction.thetaSummand_contDiff L φ x).continuous_iteratedFDeriv (by simp)).continuousOn)
      (fun x => C * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) *
        Real.exp (-d * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖))
      (fun x => by positivity) hM (fun x p hp => hbound k hk x p hp) a

end Construction

end

end OAI.Analysis.Theta.GaussianConvergence
