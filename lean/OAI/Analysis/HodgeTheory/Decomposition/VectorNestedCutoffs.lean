import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoffGradient
import OAI.Analysis.HodgeTheory.Decomposition.VectorTestDensity

/-! # Vector Nested Cutoffs -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs.Constructions

noncomputable section

/-! A cutoff equal to one near the support of another cutoff leaves both
the localized function and its weak metric equation unchanged. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem vectorCutoffGradientMultiply_coe (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g u x =
      ∑ i, VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion i ((∂_{b i} g : 𝓢(E, ℂ)) x • u x) := by
  rw [VectorCutoffInsertion.Constructions.vectorCutoffGradientMultiply_sum]
  let term := fun i => (VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion i).compLpL 2 (volume : Measure E)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u)
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      term i x = VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion i ((∂_{b i} g : 𝓢(E, ℂ)) x • u x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion i).coeFn_compLpL
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u),
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe (∂_{b i} g : 𝓢(E, ℂ)) u] with x hT hg
    exact hT.trans (congrArg (VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion i) hg)
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lp_coe_finsetSum term Finset.univ, hc] with x hs hx
  exact hs.trans (Finset.sum_congr rfl (fun i _ => hx i))

omit [CompleteSpace F] in
theorem vectorCutoffGradientMultiply_zero_on_locally_one (b : OrthonormalBasis ι ℝ E)
    (η : 𝓢(E, ℂ)) {S : Set E} (hη : ∀ x ∈ S, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ S → VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b η u x = 0 := by
  filter_upwards [vectorCutoffGradientMultiply_coe b η u] with x hx
  intro hxS
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  have hd : (∂_{b i} η : 𝓢(E, ℂ)) x = 0 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, (hη x hxS).fderiv_eq]
    change (fderiv ℝ (Function.const E (1 : ℂ)) x) (b i) = 0
    rw [fderiv_const]
    rfl
  rw [hd, zero_smul, map_zero]

theorem vectorSobolevGradient_cutoff_eq_on (b : OrthonormalBasis ι ℝ E)
    (η : 𝓢(E, ℂ)) {S : Set E} (hη : ∀ x ∈ S, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ S →
      VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 η u) x = VectorGradient.Constructions.vectorSobolevGradient (F := F) b u x := by
  rw [VectorCutoffGradient.Constructions.vectorSobolevGradient_cutoff]
  filter_upwards [Lp.coeFn_add (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b η (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply η (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)),
    vectorCutoffGradientMultiply_zero_on_locally_one b η hη
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u),
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe η (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u)] with x hadd hK hS
  intro hx
  have hηx : η x = 1 := (hη x hx).eq_of_nhds
  rw [hadd, Pi.add_apply, hK hx, hS, hηx, one_smul, zero_add]

omit [Fintype ι] [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem vectorSobolevCutoffCLM_nested (n : ℕ) (g η : 𝓢(E, ℂ))
    (hη : ∀ x ∈ tsupport g, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp F 2 (volume : Measure E)) :
    VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM n g (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM n η u) = VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM n g u := by
  apply VectorCutoffOperator.Constructions.vectorSobolevDistributionCLM_injective (n : ℝ)
  simp only [VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM_distribution]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply η.hasTemperateGrowth g.hasTemperateGrowth]
  have hmul : (η : E → ℂ) * (g : E → ℂ) = (g : E → ℂ) := by
    funext x
    change η x * g x = g x
    by_cases hx : g x = 0
    · rw [hx, mul_zero]
    · have hηx : η x = 1 := (hη x ((subset_tsupport g) hx)).eq_of_nhds
      rw [hηx, one_mul]
  rw [hmul]

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs.Constructions
