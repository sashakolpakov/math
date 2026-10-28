import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceBounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence

/-! # Vector Difference Convergence -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceConvergence.Constructions

noncomputable section

section

/-! Fourier multipliers of the genuine vector Sobolev embedding and
weak first derivatives, with their actual L² representatives. -/

open _root_.MeasureTheory FourierTransform
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevL2Embedding_fourier_coe {s : ℝ} (hs : 0 ≤ s) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding hs u) : Lp F 2 volume) x =
      (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • (𝓕 u : Lp F 2 volume) x :=
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.negative_besselSymbol_bound hs) u _
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution hs u)

theorem vectorSobolevL2Derivative_fourier_coe (m : E) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), (𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp F 2 volume) x =
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) •
        (𝓕 u : Lp F 2 volume) x := by
  let κ : ℂ := 2 * Real.pi * Complex.I
  let M := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier (F := F) (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound m)
  have hEq : 𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u) = κ • 𝓕 (M u) :=
    (Lp.fourierTransformₗᵢ E F).map_smul κ (M u)
  have hM : ∀ᵐ x ∂(volume : Measure E), (𝓕 (M u) : Lp F 2 volume) x =
      Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) • (𝓕 u : Lp F 2 volume) x :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization.CM.Construction.fourierMultiplier_l2_fourier_coeFn (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) u (M u)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.l2FourierMultiplier_distribution (by fun_prop) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.normalizedDerivativeSymbol_bound m) u)
  rw [hEq]
  filter_upwards [Lp.coeFn_smul κ (𝓕 (M u)), hM] with x hx hm
  rw [hx, Pi.smul_apply, hm, smul_smul]
  apply congrArg (fun c : ℂ => c • (𝓕 u : Lp F 2 volume) x)
  simp only [κ, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol, Complex.ofReal_mul,
    Complex.ofReal_ofNat, real_inner_comm m x]
  ring

end

/-! Genuine vector difference quotients converge strongly in L² to the
weak derivative of the function specified by its H¹ Bessel coordinate. -/

open _root_.MeasureTheory FourierTransform Filter
open scoped _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

theorem vectorL2DifferenceQuotient_tendsto_derivative (m : E) (u : Lp F 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => VectorDifferences.Constructions.vectorL2DifferenceQuotient m t
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)) (𝓝[≠] 0)
      (𝓝 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u)) := by
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  let q : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)
  let c : ℝ := 2 * Real.pi * ‖m‖
  let f : ℝ → E → F := fun t x => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x) • (𝓕 u : Lp F 2 volume) x
  let f₀ : E → F := fun x => (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x) • (𝓕 u : Lp F 2 volume) x
  have hcoef (x : E) : Tendsto (fun t : ℝ => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x)
      (𝓝[≠] 0) (𝓝 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x)) :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol_tendsto (inner ℝ m x)).mul_const (q x)
  have hcoefBound (x : E) : ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x‖ ≤ c :=
    le_of_tendsto (hcoef x).norm (Filter.Eventually.of_forall (fun t => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction.differenceQuotient_bessel_bound m x t))
  have hF (t : ℝ) : (𝓕 (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (J u)) : Lp F 2 volume) =ᵐ[volume] f t := by
    filter_upwards [VectorDifferences.Constructions.fourier_vectorL2DifferenceQuotient_coe m t (J u),
      vectorSobolevL2Embedding_fourier_coe (by norm_num : (0 : ℝ) ≤ 1) u] with x hd hJ
    rw [hd, hJ]
    exact (mul_smul _ _ _).symm
  have hlim : ∀ᵐ x ∂(volume : Measure E), Tendsto (fun t : ℝ => f t x) (𝓝[≠] 0) (𝓝 (f₀ x)) :=
    Filter.Eventually.of_forall (fun x => (hcoef x).smul_const _)
  have hb : MemLp (fun x => c * ‖(𝓕 u : Lp F 2 volume) x‖) 2 (volume : Measure E) :=
    (Lp.memLp (𝓕 u : Lp F 2 volume)).norm.const_smul c
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ x ∂(volume : Measure E),
      ‖f t x‖ ≤ c * ‖(𝓕 u : Lp F 2 volume) x‖ :=
    Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun x => by
      change ‖(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceQuotients.CM.Construction.differenceQuotientSymbol t (inner ℝ m x) * q x) • (𝓕 u : Lp F 2 volume) x‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds.CM.Construction.differenceQuotient_bessel_bound m x t) (norm_nonneg _)))
  have hbound₀ : ∀ᵐ x ∂(volume : Measure E), ‖f₀ x‖ ≤ c * ‖(𝓕 u : Lp F 2 volume) x‖ :=
    Filter.Eventually.of_forall (fun x => by
      change ‖(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion.CM.Construction.fourierDerivativeSymbol m x * q x) • (𝓕 u : Lp F 2 volume) x‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hcoefBound x) (norm_nonneg _))
  have hfourier := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpDominated.CM.Construction.l2_tendsto_dominated_representatives
    (fun t : ℝ => (𝓕 (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (J u)) : Lp F 2 volume))
    (𝓕 (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp F 2 volume) f f₀ hF
    (vectorSobolevL2Derivative_fourier_coe m u) _ hb hbound hbound₀ hlim
  have h := (Lp.fourierTransformₗᵢ E F).symm.continuous.tendsto _ |>.comp hfourier
  have hInv (w : Lp F 2 (volume : Measure E)) : (Lp.fourierTransformₗᵢ E F).symm (𝓕 w) = w :=
    (Lp.fourierTransformₗᵢ E F).symm_apply_apply w
  simpa only [Function.comp_def, hInv] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceConvergence.Constructions
