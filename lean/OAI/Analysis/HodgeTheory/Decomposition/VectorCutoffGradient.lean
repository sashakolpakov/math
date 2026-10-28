import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential
import OAI.Analysis.HodgeTheory.Decomposition.VectorGradient

/-! # Vector Cutoff Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffGradient.Constructions

noncomputable section

/-! The first-order commutator of cutoff multiplication and the genuine
Sobolev gradient factors through the underlying L2 function. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorCutoffGradientComponents (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    Lp F 2 (volume : Measure E) →L[ℂ] PiLp 2 (fun _ : ι => Lp F 2 (volume : Measure E)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp F 2 (volume : Measure E))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ))))

omit [CompleteSpace F] in
theorem vectorCutoffGradientComponents_apply (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) (i : ι) :
    vectorCutoffGradientComponents b g u i =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u := rfl

def vectorCutoffGradientMultiply (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E) :=
  (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E))).comp (vectorCutoffGradientComponents b g)

theorem vectorSobolevNormalizedGradient_cutoff (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) (i : ι) :
    VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) i =
      vectorCutoffGradientComponents b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) i +
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i) := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  have h := congrArg (fun w : Lp F 2 (volume : Measure E) =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • w) (VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_derivative g (b i) u)
  rw [VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative, VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient_derivative] at h
  simpa only [vectorCutoffGradientComponents_apply, smul_add, map_smul, smul_smul,
    inv_mul_cancel₀ hκ, one_smul] using h

omit [CompleteSpace F] in
theorem finiteLpSynthesis_schwartz_multiply
    (g : 𝓢(E, ℂ)) (u v : PiLp 2 (fun _ : ι => Lp F 2 (volume : Measure E)))
    (h : ∀ i, v i = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (u i)) :
    FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) v =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) u) := by
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i, (v i) x = g x • (u i) x := by
    apply ae_all_iff.mpr
    intro i
    rw [h i]
    exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (u i)
  apply Lp.ext
  filter_upwards [FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) v,
    FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) u,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) u), hc]
    with x hv hu hg hx
  rw [hv, hg, hu]
  apply PiLp.ext
  exact hx

/-- Leibniz's rule in the completed H1 space, with a bounded L2 commutator. -/
theorem vectorSobolevGradient_cutoff (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) :
    VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) =
      vectorCutoffGradientMultiply (F := F) b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) := by
  let w := VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) -
    vectorCutoffGradientComponents b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)
  have hw (i : ι) : w i = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i) := by
    change VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) i -
      vectorCutoffGradientComponents b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) i = _
    rw [vectorSobolevNormalizedGradient_cutoff, add_sub_cancel_left]
  have h := finiteLpSynthesis_schwartz_multiply g (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) w hw
  change FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E))
    (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) -
      vectorCutoffGradientComponents b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)) = _ at h
  rw [map_sub] at h
  change VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) -
    vectorCutoffGradientMultiply (F := F) b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) at h
  exact sub_eq_iff_eq_add'.mp h

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffGradient.Constructions
