import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient

/-! # Strong Sobolev Operators -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison

noncomputable section

/-! Bounded operators which commute with actual spatial differences preserve
all orders of strong Sobolev regularity. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [Fintype ι]

theorem StrongSobolev.CM.Construction.HasStrongSobolevDerivatives.map (b : OrthonormalBasis ι ℝ E)
    (T : Lp F 2 (volume : Measure E) →L[ℝ] Lp G 2 (volume : Measure E))
    (hT : ∀ i : ι, ∀ t : ℝ, ∀ u : Lp F 2 (volume : Measure E),
      DifferenceProduct.CM.Construction.realL2Difference (b i) t (T u) = T (DifferenceProduct.CM.Construction.realL2Difference (b i) t u))
    (n : ℕ) {u : Lp F 2 (volume : Measure E)} (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (T u) := by
  induction n generalizing u with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hu.1, fun i => ?_⟩
    obtain ⟨du, hdu, ⟨B, hB⟩, hduN⟩ := hu.2 i
    refine ⟨T du, ?_, ⟨‖T‖ * B, fun t => ?_⟩, ih hduN⟩
    · simpa only [hT, Function.comp_def] using (T.continuous.tendsto du).comp hdu
    · rw [hT]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _))

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] in
theorem StrongSobolevOperators.CM.Construction.strongSobolev_vectorGradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) := by
  apply hu.map b ((EuclideanGradient.CM.Construction.sobolevVectorGradient b).restrictScalars ℝ) _ n
  intro i t w
  change DifferenceProduct.CM.Construction.realL2Difference (b i) t (EuclideanGradient.CM.Construction.sobolevVectorGradient b w) =
    EuclideanGradient.CM.Construction.sobolevVectorGradient b (DifferenceProduct.CM.Construction.realL2Difference (b i) t w)
  rw [DifferenceProduct.CM.Construction.realL2Difference_eq_complex, EuclideanGradient.CM.Construction.sobolevVectorGradient_difference]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
