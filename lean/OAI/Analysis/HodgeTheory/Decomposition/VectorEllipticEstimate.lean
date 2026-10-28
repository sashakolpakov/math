import OAI.Analysis.HodgeTheory.Decomposition.VectorGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Vector Elliptic Estimate -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticEstimate.Constructions

noncomputable section

/-! The genuine difference-quotient estimate for vector elliptic systems
under an integrated Gårding inequality, including a lower-order L² term. -/

open _root_.MeasureTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The actual weak equation with an additional vector-valued flux forcing.
Such terms arise when multiplying a weak solution by a spatial cutoff. -/
def IsVectorWeakFluxSolution (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (u f : Lp F 2 (volume : Measure E))
    (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E)) : Prop :=
  ∀ v : Lp F 2 (volume : Measure E),
    (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) =
      inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v) +
        inner ℝ g (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v)

theorem vector_elliptic_flux_test_inner (b : OrthonormalBasis ι ℝ E) (m : E) (t : ℝ)
    (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E)) (v : Lp F 2 (volume : Measure E)) :
    inner ℝ g (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) =
      inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v) := by
  rw [map_neg, VectorGradient.Constructions.vectorSobolevGradient_difference, inner_neg_right, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_inner]

/-- The gradient of every spatial difference quotient of an actual weak
solution has a bound independent of the nonzero translation size. -/
theorem vector_elliptic_flux_difference_gradient_bound (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F)) {L : NNReal}
    (hA : LipschitzWith L A) {C a c : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hc : 0 ≤ c)
    (hgard : ∀ y : E, ∀ v : Lp F 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ ≤
        (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) +
          c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2)
    (u f : Lp F 2 (volume : Measure E))
    (g : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : IsVectorWeakFluxSolution b A u f g)
    (m : E) {B₀ : ℝ} (hg : ∀ t : ℝ, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g‖ ≤ B₀) :
    ∃ B : ℝ, ∀ t : ℝ, ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u)‖ ≤ B := by
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := F) b
  let k : ℝ := 2 * Real.pi * ‖m‖
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hAm : AEStronglyMeasurable A (volume : Measure E) := hA.continuous.aestronglyMeasurable
  have hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  let M := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hAm hCm
  have hweak (v : Lp F 2 (volume : Measure E)) :
      inner ℝ (M (D u)) (D v) = inner ℝ f (J v) + inner ℝ g (D v) :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hAm hCm (D u) (D v)).trans (hsol v)
  let P : ℝ := (L : ℝ) * ‖m‖ * ‖D u‖ + k * ‖f‖ + max B₀ 0
  let Q : ℝ := k ^ 2 * ‖f‖ * ‖u‖ + c * (k * ‖u‖) ^ 2
  refine ⟨1 + (P + Q) / a, fun t => ?_⟩
  let v := VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u
  let T := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient A (t • m))
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
  let R := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient A m t)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
  have hprod : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (M (D u)) = T (D v) + R (D u) := by
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_coefficient_product]
    rw [← VectorGradient.Constructions.vectorSobolevGradient_difference]
  have htest : inner ℝ (T (D v)) (D v) + inner ℝ (R (D u)) (D v) =
      inner ℝ f (J (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) +
        inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) := by
    calc
      _ = inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (M (D u))) (D v) := by rw [hprod, inner_add_left]
      _ = -inner ℝ (M (D u)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m (-t) (D v)) := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_inner m t _ _
      _ = inner ℝ (M (D u)) (D (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) := by
        rw [map_neg, VectorGradient.Constructions.vectorSobolevGradient_difference b m (-t) v, inner_neg_right]
      _ = inner ℝ f (J (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) +
          inner ℝ g (D (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) := hweak _
      _ = _ := by
        rw [vector_elliptic_flux_test_inner b m t g v]
  have hlow : a * ‖D v‖ * ‖D v‖ ≤ inner ℝ (T (D v)) (D v) + c * ‖J v‖ ^ 2 := by
    have heq : inner ℝ (T (D v)) (D v) =
        ∫ x, inner ℝ (A (x + t • m) (D v x)) (D v x) :=
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m))
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m)) (D v) (D v)
    rw [heq]
    exact hgard (t • m) v
  have hR : ‖R (D u)‖ ≤ ((L : ℝ) * ‖m‖) * ‖D u‖ :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
      (Filter.Eventually.of_forall (fun x => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hA m x t)) (D u)
  have hJv : ‖J v‖ ≤ k * ‖u‖ := by
    change ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding _ (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u)‖ ≤ _
    rw [← VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolevEmbedding_comm]
    exact VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolev_bound m t u
  have hzero : c * ‖J v‖ ^ 2 ≤ c * (k * ‖u‖) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hJv 2) hc
  have hv : ‖v‖ ≤ k * ‖u‖ + ‖D v‖ := by
    have hgraph := VectorGradient.Constructions.vectorSobolevGradient_graph_bound b v
    change ‖v‖ ≤ ‖J v‖ + ‖D v‖ at hgraph
    linarith
  have hJtest : ‖J (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))‖ ≤ k * ‖v‖ := by
    rw [map_neg, norm_neg]
    change ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding _ (VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v)‖ ≤ _
    rw [← VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolevEmbedding_comm]
    exact VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolev_bound m (-t) v
  have hright : inner ℝ f (J (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) ≤
      ‖f‖ * (k * (k * ‖u‖ + ‖D v‖)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (hJtest.trans (mul_le_mul_of_nonneg_left hv hk)) (norm_nonneg _))
  have hcross : -inner ℝ (R (D u)) (D v) ≤ ((L : ℝ) * ‖m‖ * ‖D u‖) * ‖D v‖ := by
    have h := real_inner_le_norm (-(R (D u))) (D v)
    rw [inner_neg_left, norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hflux : inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) ≤ max B₀ 0 * ‖D v‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((hg t).trans (le_max_left _ _)) (norm_nonneg _))
  have hquad : a * ‖D v‖ * ‖D v‖ ≤ P * ‖D v‖ + Q := by
    calc
      _ ≤ inner ℝ (T (D v)) (D v) + c * ‖J v‖ ^ 2 := hlow
      _ = inner ℝ f (J (-(VectorDifferences.Constructions.vectorL2DifferenceQuotient m (-t) v))) +
          inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) - inner ℝ (R (D u)) (D v) + c * ‖J v‖ ^ 2 := by linarith [htest]
      _ ≤ ‖f‖ * (k * (k * ‖u‖ + ‖D v‖)) + max B₀ 0 * ‖D v‖ +
          ((L : ℝ) * ‖m‖ * ‖D u‖) * ‖D v‖ + c * (k * ‖u‖) ^ 2 :=
            add_le_add (add_le_add (add_le_add hright hflux) hcross) hzero
      _ = P * ‖D v‖ + Q := by dsimp [P, Q]; ring
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction.quadratic_energy_bound ha (by dsimp [P]; positivity) (by dsimp [Q]; positivity)
    (norm_nonneg _) hquad

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticEstimate.Constructions
