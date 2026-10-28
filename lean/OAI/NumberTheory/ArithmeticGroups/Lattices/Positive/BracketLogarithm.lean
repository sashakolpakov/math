import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSquareRoot
import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential

/-! # Bracket Logarithm -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketLogarithm.Construction

noncomputable section

/-! Every positive self-adjoint bracket automorphism is the
exponential of a self-adjoint derivation. -/

open NormedSpace

theorem positive_bilinear_preserver_logarithm
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (g : L →L[ℝ] L) (hsym : g.toLinearMap.IsSymmetric)
    (hpos : ∀ x : L, x ≠ 0 → 0 < inner ℝ (g x) x)
    (hB : ∀ x y, g (B x y) = B (g x) (g y)) :
    ∃ D : L →L[ℝ] L, D.toLinearMap.IsSymmetric ∧
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B D = 0 ∧ exp D = g := by
  let b := hsym.eigenvectorBasis (n := Module.finrank ℝ L) rfl
  let w := hsym.eigenvalues (n := Module.finrank ℝ L) rfl
  have hg (i : Fin (Module.finrank ℝ L)) : g (b i) = w i • b i :=
    hsym.apply_eigenvectorBasis rfl i
  have hw (i : Fin (Module.finrank ℝ L)) : 0 < w i := by
    have hi := hpos (b i) (b.toBasis.ne_zero i)
    rw [hg, real_inner_smul_left, b.inner_eq_one, mul_one] at hi
    exact hi
  let D := (BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis (fun i => Real.log (w i))).toContinuousLinearMap
  refine ⟨D, BasisSpectralOperator.Construction.basisSpectralEnd_isSymmetric b _, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    have hd := BracketSpectralFunctions.Construction.positive_eigenbasis_log_derivation (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B) b.toBasis
      g.toLinearMap w hg hw hB x y
    change D (B x y) = B (D x) y + B x (D y) at hd
    rw [Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect_apply, hd]
    simp only [zero_apply]
    abel
  · change exp (BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis (fun i => Real.log (w i))).toContinuousLinearMap = g
    rw [SpectralOperatorExponential.Construction.basisSpectralEnd_exp]
    have he : BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis (fun i => exp (Real.log (w i))) = g.toLinearMap := by
      apply BasisSpectralOperator.Construction.basisSpectralEnd_eq_of_eigenbasis
      intro i
      rw [← Real.exp_eq_exp_ℝ, Real.exp_log (hw i)]
      exact hg i
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun he x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketLogarithm.Construction
