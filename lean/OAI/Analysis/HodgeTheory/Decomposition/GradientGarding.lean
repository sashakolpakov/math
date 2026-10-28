import OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevDensity
import OAI.Analysis.HodgeTheory.Decomposition.VectorGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Gradient Garding -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GradientGarding.Constructions

noncomputable section

/-! Extension of genuine gradient estimates by smooth density and stability
of their integrated coercivity under uniformly small coefficient changes. -/

open _root_.MeasureTheory
open scoped SchwartzMap
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction

section Perturbation

variable {E G : Type*} [MeasurableSpace E] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] {μ : Measure E}

theorem boundedFieldEnergy_perturbation (A₀ : G →L[ℝ] G) (A : E → G →L[ℝ] G)
    (hA : AEStronglyMeasurable A μ) {C ε : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    (hε : ∀ᵐ x ∂μ, ‖A₀ - A x‖ ≤ ε) (u : Lp G 2 μ) :
    (∫ x, inner ℝ (A₀ (u x)) (u x) ∂μ) ≤
      (∫ x, inner ℝ (A x (u x)) (u x) ∂μ) + ε * ‖u‖ ^ 2 := by
  let B := fun x => A₀ - A x
  have hB : AEStronglyMeasurable B μ := aestronglyMeasurable_const.sub hA
  let M := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) B hB hε
  have hn : ‖M u‖ ≤ ε * ‖u‖ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLinear_norm_le B hB hε u
  have hp : inner ℝ (M u) u ≤ ε * ‖u‖ ^ 2 := by
    calc
      _ ≤ ‖M u‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ (ε * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := by ring
  have heq : (∫ x, inner ℝ (A₀ (u x)) (u x) ∂μ) =
      (∫ x, inner ℝ (A x (u x)) (u x) ∂μ) + inner ℝ (M u) u := by
    change _ = _ + AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy B hB hε u u
    rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply, ← integral_add
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_integrable A hA hC u u) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_integrable B hB hε u u)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [B, sub_apply, inner_sub_left]
      ring)
  rw [heq]
  exact add_le_add le_rfl hp

end Perturbation

variable {E κ ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [Fintype κ]

theorem gradientEnergy_continuous (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) →L[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ))
    (hA : AEStronglyMeasurable A (volume : Measure E)) {C : ℝ}
    (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C) :
    Continuous (fun u : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E) =>
      ∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) := by
  have h : Continuous (fun u : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E) =>
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hA hC (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u)) :=
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hA hC).continuous.comp (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b).continuous).clm_apply
      (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b).continuous
  simpa only [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply] using h

theorem gradient_garding_of_schwartz (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) →L[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ))
    (hA : AEStronglyMeasurable A (volume : Measure E)) {C a c : ℝ}
    (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (h : ∀ f : 𝓢(E, EuclideanSpace ℂ κ),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)‖ ^ 2 ≤
        (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x))
          (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f) x)) +
        c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f)‖ ^ 2)
    (u : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E)) :
    a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u‖ ^ 2 ≤
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) +
      c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ ^ 2 := by
  have hclosed : IsClosed {v : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E) |
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b v‖ ^ 2 ≤
        (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b v x)) +
        c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2} :=
    isClosed_le ((VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b).continuous.norm.pow 2 |>.const_mul a)
      ((gradientEnergy_continuous b A hA hC).add
        ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)).continuous.norm.pow 2 |>.const_mul c))
  exact (VectorSobolevDensity.Constructions.vectorSchwartzSobolevCoordinate_denseRange 1).induction_on u hclosed h

theorem gradient_garding_small_perturbation (b : OrthonormalBasis ι ℝ E)
    (A₀ : PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) →L[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ))
    (A : E → PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) →L[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ))
    (hA : AEStronglyMeasurable A (volume : Measure E)) {C a ε : ℝ}
    (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (hε : ∀ x, ‖A₀ - A x‖ ≤ ε)
    (h₀ : ∀ u : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u‖ ^ 2 ≤
        ∫ x, inner ℝ (A₀ (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x))
    (y : E) (u : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E)) :
    (a - ε) * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u‖ ^ 2 ≤
      ∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x) := by
  have h := (h₀ u).trans (boundedFieldEnergy_perturbation A₀ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient A y)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hA y) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_bound A hC y)
    (Filter.Eventually.of_forall (fun x => hε (x + y))) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u))
  change a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u‖ ^ 2 ≤
    (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x)) +
      ε * ‖VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u‖ ^ 2 at h
  nlinarith only [h]

end

end OAI.Analysis.HodgeTheory.Decomposition.GradientGarding.Constructions
