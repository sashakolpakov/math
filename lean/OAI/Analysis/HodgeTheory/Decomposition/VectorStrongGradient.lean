import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts

/-! # Vector Strong Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorStrongGradient.Constructions

noncomputable section

/-! All-order strong regularity of actual vector gradients and their
products with derivatives of smooth principal coefficient fields. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorStrongSobolev_gradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    {u : Lp F 2 (volume : Measure E)} (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) := by
  apply hu.map b ((VectorGradient.Constructions.vectorSobolevGradient (F := F) b).restrictScalars ℝ) _ n
  intro i t w
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference (b i) t (VectorGradient.Constructions.vectorSobolevGradient (F := F) b w) =
    VectorGradient.Constructions.vectorSobolevGradient (F := F) b (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference (b i) t w)
  rw [VectorLocalElliptic.Constructions.realL2Difference_eq_vector (b i) t w, VectorGradient.Constructions.vectorSobolevGradient_difference]

theorem vectorStrongSobolev_gradient_of_memSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (u : Lp F 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) := by
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff,
    show -(1 : ℝ) + ((n : ℝ) + 1) = n by ring] at hu
  exact vectorStrongSobolev_gradient b n ((VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b n u).mpr hu)

theorem vectorStrongSobolev_derivative_coefficient_gradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (c : PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) (i : ι)
    (u : Lp F 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 2) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative A (b i))
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_continuous A hA (b i)).aestronglyMeasurable
        (Filter.Eventually.of_forall (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i)))
        (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)) := by
  have hdA := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_smooth A hA (b i)
  have hdAc : HasCompactSupport (fun x => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative A (b i) x - 0) := by
    simpa only [sub_zero] using AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_compact_support A c hc (b i)
  obtain ⟨Ld, hLd⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives.CM.Construction.coefficientDerivative_lipschitz A c hA hc (b i)
  apply AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b (n + 1) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative A (b i)) 0 hdA hdAc hLd
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction.coefficientDerivative_bound A (hA.differentiable (by simp)) hL (b i))
  apply vectorStrongSobolev_gradient_of_memSobolev b (n + 1) u
  simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hu

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorStrongGradient.Constructions
