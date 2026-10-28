import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffGradient

/-! # Vector Cutoff Insertion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffInsertion.Constructions

noncomputable section

/-! The actual vector cutoff-gradient commutator is a finite sum of
fixed coefficient insertions composed with scalar Schwartz multipliers. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

def vectorCutoffGradientInsertion (i : ι) : F →L[ℝ] PiLp 2 (fun _ : ι => F) := by
  classical
  exact ((FiniteLp.Constructions.finiteHilbertSingle (𝕜 := ℂ) i).comp
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ContinuousLinearMap.id ℂ F)).restrictScalars ℝ

theorem vectorCutoffGradientInsertion_compLpL (i : ι) (u : Lp F 2 (volume : Measure E)) :
    letI := Classical.decEq ι
    (FiniteLp.Constructions.finiteHilbertSingle (𝕜 := ℂ) i).compLpL 2 volume ((2 * Real.pi * Complex.I : ℂ)⁻¹ • u) =
      (vectorCutoffGradientInsertion (F := F) i).compLpL 2 volume u := by
  classical
  apply Lp.ext
  filter_upwards [(FiniteLp.Constructions.finiteHilbertSingle (𝕜 := ℂ) i).coeFn_compLpL
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • u),
    Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ)⁻¹ u,
    (vectorCutoffGradientInsertion (F := F) i).coeFn_compLpL u] with x hL hs hR
  rw [hL, hR, hs]
  rfl

theorem vectorCutoffGradientMultiply_sum (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) :
    VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g u = ∑ i,
      (vectorCutoffGradientInsertion (F := F) i).compLpL 2 volume
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u) := by
  classical
  change FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) (VectorCutoffGradient.Constructions.vectorCutoffGradientComponents b g u) = _
  simp only [FiniteLp.Constructions.finiteLpSynthesis, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, (FiniteLp.Constructions.finiteHilbertSingle (𝕜 := ℂ) i).compLpL 2 volume
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u)) = _
  exact Finset.sum_congr rfl (fun i _ => vectorCutoffGradientInsertion_compLpL i _)

theorem vectorCutoffGradientMultiply_operator_sum (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g).restrictScalars ℝ = ∑ i,
      ((vectorCutoffGradientInsertion (F := F) i).compLpL 2 (volume : Measure E)).comp
        ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) (∂_{b i} g : 𝓢(E, ℂ))).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    using vectorCutoffGradientMultiply_sum b g u

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffInsertion.Constructions
