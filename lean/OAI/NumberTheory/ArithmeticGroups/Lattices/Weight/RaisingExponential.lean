import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Raising Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential.Construction

noncomputable section

/-! Exponentials of weight-raising derivations belong to the closed
unipotent bracket subgroup. -/

open NormedSpace

theorem exp_sub_one_mem_closed_multiplicative_submodule
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (W : Submodule ℝ A) (hW : IsClosed (W : Set A))
    (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W) (x : A) (hx : x ∈ W) : exp x - 1 ∈ W := by
  have hp (n : ℕ) : x ^ (n + 1) ∈ W := by
    induction n with
    | zero => simpa only [zero_add, pow_one] using hx
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ ih x hx
  have he : exp x = 1 + ∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • x ^ (n + 1) := by
    rw [exp_eq_tsum ℝ]
    simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] using
      (expSeries_summable' (𝕂 := ℝ) x).tsum_eq_zero_add
  rw [he, add_sub_cancel_left]
  exact tsum_mem hW (fun n => W.smul_mem _ (hp n))

theorem weightRaising_exp_sub_one_mem
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) : exp X - 1 ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  exact exp_sub_one_mem_closed_multiplicative_submodule (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w).closed_of_finiteDimensional
    (fun A hA C hC => RaisingMultiplication.Construction.weightRaisingOperators_mul b w A C hA hC) X hX

theorem positive_derivation_exp_mem_unipotent
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (X : L →L[ℝ] L) (hX : X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H) :
    (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv X).toUnit ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have hXD : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 := InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _ hX
  constructor
  · exact Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B X ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B X).mp hXD)
  · exact weightRaising_exp_sub_one_mem b w X (Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B b H hH w heig hX)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential.Construction
