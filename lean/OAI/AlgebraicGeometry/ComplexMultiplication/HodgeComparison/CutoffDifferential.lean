import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevSmoothDensity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient

/-! # Cutoff Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

noncomputable section

section

/-! Actual L2 cutoff multiplication and its weak first derivative. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def l2ScalarMultiply (g : Lp ℂ ⊤ μ) : Lp F 2 μ →L[ℂ] Lp F 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => g • u
      map_add' := fun u v => Lp.add_smul g u v
      map_smul' := fun c u => (Lp.smul_comm c g u).symm }
    ‖g‖ (fun u => Lp.norm_smul_le g u)

theorem l2ScalarMultiply_coe (g : Lp ℂ ⊤ μ) (u : Lp F 2 μ) :
    l2ScalarMultiply g u =ᵐ[μ] fun x => g x • u x := Lp.coeFn_lpSMul g u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzL2Multiply (g : 𝓢(E, ℂ)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  l2ScalarMultiply ((g.memLp_top volume).toLp g)

theorem schwartzL2Multiply_coe (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    schwartzL2Multiply g u =ᵐ[volume] fun x => g x • u x := by
  filter_upwards [l2ScalarMultiply_coe ((g.memLp_top volume).toLp g) u,
    (g.memLp_top volume).coeFn_toLp] with x hx hg
  exact hx.trans (congrArg (fun c : ℂ => c • u x) hg)

variable [CompleteSpace F]

theorem schwartzL2Multiply_distribution (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    (schwartzL2Multiply g u : 𝓢'(E, F)) = smulLeftCLM F g (u : 𝓢'(E, F)) :=
  Lp.toTemperedDistribution_smul_eq g.hasTemperateGrowth (g.memLp_top volume) u

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] in
theorem sobolevCutoffCLM_embedding (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E)) :
    SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) =
      schwartzL2Multiply g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : 𝓢'(E, ℂ)) =
    (schwartzL2Multiply g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) : 𝓢'(E, ℂ))
  rw [schwartzL2Multiply_distribution, SobolevIs.CM.Construction.sobolevL2Embedding_distribution,
    SobolevIs.CM.Construction.sobolevL2Embedding_distribution]
  simpa only [Nat.cast_one, SobolevCutoffOperator.CM.Construction.sobolevDistributionCLM, ContinuousLinearMap.comp_apply,
    Lp.toTemperedDistributionCLM_apply] using SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM_distribution 1 g u

omit [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] in
theorem sobolevCutoffCLM_derivative (g : 𝓢(E, ℂ)) (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    SobolevDifferential.CM.Construction.sobolevL2Derivative m (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) =
      schwartzL2Multiply (∂_{m} g : 𝓢(E, ℂ))
        (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
      schwartzL2Multiply g (SobolevDifferential.CM.Construction.sobolevL2Derivative m u) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change (SobolevDifferential.CM.Construction.sobolevL2Derivative m (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : 𝓢'(E, ℂ)) =
    ((schwartzL2Multiply (∂_{m} g : 𝓢(E, ℂ))
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
      schwartzL2Multiply g (SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp ℂ 2 volume) : 𝓢'(E, ℂ))
  rw [SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, sobolevCutoffCLM_embedding,
    schwartzL2Multiply_distribution, SobolevInv.CM.Construction.distribution_cutoff_leibniz]
  have hadd (v w : Lp ℂ 2 (volume : Measure E)) :
      ((v + w : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ)) + (w : 𝓢'(E, ℂ)) := by
    simpa only [Lp.toTemperedDistributionCLM_apply] using
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2).map_add v w
  rw [hadd, schwartzL2Multiply_distribution, schwartzL2Multiply_distribution,
    SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution]

end

/-! The first-order commutator of cutoff multiplication and the genuine
Sobolev gradient factors through the underlying L2 function. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def cutoffGradientComponents (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 (volume : Measure E))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ))))

theorem cutoffGradientComponents_apply (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp ℂ 2 (volume : Measure E)) (i : ι) :
    cutoffGradientComponents b g u i =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u := rfl

def cutoffGradientMultiply (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E) :=
  (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ)).comp (cutoffGradientComponents b g)

theorem sobolevNormalizedGradient_cutoff (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp ℂ 2 (volume : Measure E)) (i : ι) :
    FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) i =
      cutoffGradientComponents b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) i +
        schwartzL2Multiply g (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i) := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  have h := congrArg (fun w : Lp ℂ 2 (volume : Measure E) =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • w) (sobolevCutoffCLM_derivative g (b i) u)
  rw [FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative, FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative] at h
  simpa only [cutoffGradientComponents_apply, smul_add, map_smul, smul_smul,
    inv_mul_cancel₀ hκ, one_smul] using h

theorem lpOrthonormalSynthesis_schwartz_multiply
    (g : 𝓢(E, ℂ)) (u v : PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)))
    (h : ∀ i, v i = schwartzL2Multiply g (u i)) :
    LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) v =
      schwartzL2Multiply g (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) u) := by
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i, (v i) x = g x • (u i) x := by
    apply ae_all_iff.mpr
    intro i
    rw [h i]
    exact schwartzL2Multiply_coe g (u i)
  apply Lp.ext
  filter_upwards [LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) v,
    LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) u,
    schwartzL2Multiply_coe g (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) u), hc]
    with x hv hu hg hx
  rw [hv, hg, hu, Finset.smul_sum]
  simp only [hx, smul_assoc]

/-- Leibniz's rule in the completed H1 space, with a bounded L2 commutator. -/
theorem sobolevVectorGradient_cutoff (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp ℂ 2 (volume : Measure E)) :
    EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) =
      cutoffGradientMultiply b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
        schwartzL2Multiply g (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) := by
  let w := FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) -
    cutoffGradientComponents b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)
  have hw (i : ι) : w i = schwartzL2Multiply g (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i) := by
    change FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) i -
      cutoffGradientComponents b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) i = _
    rw [sobolevNormalizedGradient_cutoff, add_sub_cancel_left]
  have h := lpOrthonormalSynthesis_schwartz_multiply g (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u) w hw
  change LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ)
    (FourierEnergy.CM.Construction.sobolevNormalizedGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) -
      cutoffGradientComponents b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)) = _ at h
  rw [map_sub] at h
  change EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) -
    cutoffGradientMultiply b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) =
      schwartzL2Multiply g (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) at h
  exact sub_eq_iff_eq_add'.mp h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction
