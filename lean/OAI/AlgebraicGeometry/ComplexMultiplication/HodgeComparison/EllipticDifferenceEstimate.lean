import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion

/-! # Elliptic Difference Estimate -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction

noncomputable section

/-! The coercive difference-quotient estimate for a genuine weak elliptic
equation with bounded Lipschitz coefficients. -/

open _root_.MeasureTheory

theorem quadratic_energy_bound {a A B x : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (_hx : 0 ≤ x) (h : a * x * x ≤ A * x + B) : x ≤ 1 + (A + B) / a := by
  by_cases hx1 : x ≤ 1
  · exact hx1.trans (le_add_of_nonneg_right (div_nonneg (add_nonneg hA hB) ha.le))
  have hxpos : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx1)
  have hB' : B ≤ B * x := by nlinarith
  have hax : a * x ≤ A + B := by
    apply (mul_le_mul_iff_right₀ hxpos).mp
    nlinarith
  have hdiv : x ≤ (A + B) / a := (le_div_iff₀ ha).mpr (by nlinarith)
  linarith

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem boundedFieldLp_norm_le_other (A : E → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (volume : Measure E)) {C L : ℝ}
    (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (hL : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ L) (u : Lp F 2 (volume : Measure E)) :
    ‖LpCoefficients.CM.Construction.boundedFieldLp A hA hC u‖ ≤ L * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC u, hL] with x hx hLx
  rw [hx]
  exact ((A x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hLx (norm_nonneg _))

variable {ι : Type*} [Fintype ι]

def IsEuclideanWeakMetricSolution (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (u f : Lp ℂ 2 (volume : Measure E)) : Prop :=
  ∀ v : Lp ℂ 2 (volume : Measure E),
    (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x)) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v x)) =
      inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v)

/-- The actual weak equation with an additional vector-valued flux forcing.
Such terms arise when multiplying a weak solution by a spatial cutoff. -/
def IsEuclideanWeakMetricFluxSolution (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (u f : Lp ℂ 2 (volume : Measure E))
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E)) : Prop :=
  ∀ v : Lp ℂ 2 (volume : Measure E),
    (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x)) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v x)) =
      inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v) +
        inner ℝ g (EuclideanGradient.CM.Construction.sobolevVectorGradient b v)

theorem elliptic_flux_test_inner (b : OrthonormalBasis ι ℝ E) (m : E) (t : ℝ)
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E)) (v : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ g (EuclideanGradient.CM.Construction.sobolevVectorGradient b (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) =
      inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t g) (EuclideanGradient.CM.Construction.sobolevVectorGradient b v) := by
  rw [map_neg, EuclideanGradient.CM.Construction.sobolevVectorGradient_difference, inner_neg_right, DifferenceProduct.CM.Construction.realL2Difference_inner]

/-- The gradient of every spatial difference quotient of an actual weak
solution has a bound independent of the nonzero translation size. -/
theorem elliptic_flux_difference_gradient_bound (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E))
    (g : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hsol : IsEuclideanWeakMetricFluxSolution b A u f g)
    (m : E) {B₀ : ℝ} (hg : ∀ t : ℝ, ‖DifferenceProduct.CM.Construction.realL2Difference m t g‖ ≤ B₀) :
    ∃ B : ℝ, ∀ t : ℝ, ‖EuclideanGradient.CM.Construction.sobolevVectorGradient b (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)‖ ≤ B := by
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  let D := EuclideanGradient.CM.Construction.sobolevVectorGradient b
  let k : ℝ := 2 * Real.pi * ‖m‖
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hAm : AEStronglyMeasurable A (volume : Measure E) := hA.continuous.aestronglyMeasurable
  have hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hAm hCm
  have hweak (v : Lp ℂ 2 (volume : Measure E)) :
      inner ℝ (M (D u)) (D v) = inner ℝ f (J v) + inner ℝ g (D v) :=
    (CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hAm hCm (D u) (D v)).trans (hsol v)
  let P : ℝ := (L : ℝ) * ‖m‖ * ‖D u‖ + k * ‖f‖ + max B₀ 0
  let Q : ℝ := k ^ 2 * ‖f‖ * ‖u‖
  refine ⟨1 + (P + Q) / a, fun t => ?_⟩
  let v := DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u
  let T := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (DifferenceProduct.CM.Construction.translatedCoefficient A (t • m))
    (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m)) (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
  let R := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) (DifferenceProduct.CM.Construction.differenceCoefficient A m t)
    (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t) (DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
  have hprod : DifferenceProduct.CM.Construction.realL2Difference m t (M (D u)) = T (D v) + R (D u) := by
    rw [DifferenceProduct.CM.Construction.realL2Difference_coefficient_product]
    rw [← EuclideanGradient.CM.Construction.sobolevVectorGradient_difference]
  have htest : inner ℝ (T (D v)) (D v) + inner ℝ (R (D u)) (D v) =
      inner ℝ f (J (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) +
        inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) := by
    calc
      _ = inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t (M (D u))) (D v) := by rw [hprod, inner_add_left]
      _ = -inner ℝ (M (D u)) (DifferenceProduct.CM.Construction.realL2Difference m (-t) (D v)) := DifferenceProduct.CM.Construction.realL2Difference_inner m t _ _
      _ = inner ℝ (M (D u)) (D (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) := by
        rw [map_neg, EuclideanGradient.CM.Construction.sobolevVectorGradient_difference b m (-t) v, inner_neg_right]
      _ = inner ℝ f (J (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) +
          inner ℝ g (D (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) := hweak _
      _ = _ := by
        rw [elliptic_flux_test_inner b m t g v]
  have hlow : a * ‖D v‖ * ‖D v‖ ≤ inner ℝ (T (D v)) (D v) :=
    CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_lower_bound _ (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m))
      (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
      (Filter.Eventually.of_forall (fun x => hpos (x + t • m))) (D v)
  have hR : ‖R (D u)‖ ≤ ((L : ℝ) * ‖m‖) * ‖D u‖ :=
    boundedFieldLp_norm_le_other _ (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
      (DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
      (Filter.Eventually.of_forall (fun x => DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hA m x t)) (D u)
  have hJv : ‖J v‖ ≤ k * ‖u‖ := by
    change ‖SobolevIs.CM.Construction.sobolevL2Embedding _ (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)‖ ≤ _
    rw [← DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevEmbedding_comm]
    exact DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolev_bound m t u
  have hv : ‖v‖ ≤ k * ‖u‖ + ‖D v‖ := by
    have hgraph := EuclideanGradient.CM.Construction.sobolevVectorGradient_graph_bound b v
    change ‖v‖ ≤ ‖J v‖ + ‖D v‖ at hgraph
    linarith
  have hJtest : ‖J (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)‖ ≤ k * ‖v‖ := by
    rw [map_neg, norm_neg]
    change ‖SobolevIs.CM.Construction.sobolevL2Embedding _ (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)‖ ≤ _
    rw [← DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevEmbedding_comm]
    exact DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolev_bound m (-t) v
  have hright : inner ℝ f (J (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) ≤
      ‖f‖ * (k * (k * ‖u‖ + ‖D v‖)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (hJtest.trans (mul_le_mul_of_nonneg_left hv hk)) (norm_nonneg _))
  have hcross : -inner ℝ (R (D u)) (D v) ≤ ((L : ℝ) * ‖m‖ * ‖D u‖) * ‖D v‖ := by
    have h := real_inner_le_norm (-R (D u)) (D v)
    rw [inner_neg_left, norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hflux : inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) ≤ max B₀ 0 * ‖D v‖ :=
    (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((hg t).trans (le_max_left _ _)) (norm_nonneg _))
  have hquad : a * ‖D v‖ * ‖D v‖ ≤ P * ‖D v‖ + Q := by
    calc
      _ ≤ inner ℝ (T (D v)) (D v) := hlow
      _ = inner ℝ f (J (-DifferenceQuotients.CM.Construction.l2DifferenceQuotient m (-t) v)) +
          inner ℝ (DifferenceProduct.CM.Construction.realL2Difference m t g) (D v) - inner ℝ (R (D u)) (D v) := by linarith [htest]
      _ ≤ ‖f‖ * (k * (k * ‖u‖ + ‖D v‖)) + max B₀ 0 * ‖D v‖ +
          ((L : ℝ) * ‖m‖ * ‖D u‖) * ‖D v‖ := add_le_add (add_le_add hright hflux) hcross
      _ = P * ‖D v‖ + Q := by dsimp [P, Q]; ring
  exact quadratic_energy_bound ha (by dsimp [P]; positivity) (by dsimp [Q]; positivity)
    (norm_nonneg _) hquad

theorem elliptic_difference_gradient_bound (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (u f : Lp ℂ 2 (volume : Measure E)) (hsol : IsEuclideanWeakMetricSolution b A u f)
    (m : E) : ∃ B : ℝ, ∀ t : ℝ, ‖EuclideanGradient.CM.Construction.sobolevVectorGradient b (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)‖ ≤ B := by
  apply elliptic_flux_difference_gradient_bound b A hA hC ha hpos u f 0 (B₀ := 0)
  · intro v
    simpa only [inner_zero_left, add_zero] using hsol v
  · exact fun t => by simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction
