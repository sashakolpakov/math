import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential

/-! # Strong Cutoff Gradient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffGradient.CM.Construction

noncomputable section

/-! The actual cutoff-gradient commutator and its Hilbert adjoint preserve
every Sobolev order. This controls both forcing terms in localization. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def cutoffGradientInsertion (i : ι) : ℂ →L[ℝ] EuclideanSpace ℂ ι :=
  ((((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.basisFun ι ℂ i)).comp
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ContinuousLinearMap.id ℂ ℂ))).restrictScalars ℝ

theorem cutoffGradientInsertion_compLpL (i : ι) (u : Lp ℂ 2 (volume : Measure E)) :
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.basisFun ι ℂ i)).compLpL 2 volume
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • u) =
      (cutoffGradientInsertion i).compLpL 2 volume u := by
  apply Lp.ext
  filter_upwards [((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.basisFun ι ℂ i)).coeFn_compLpL
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ • u),
    Lp.coeFn_smul (2 * Real.pi * Complex.I : ℂ)⁻¹ u,
    (cutoffGradientInsertion i).coeFn_compLpL u] with x hL hs hR
  rw [hL, hR, hs]
  rfl

theorem cutoffGradientMultiply_sum (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp ℂ 2 (volume : Measure E)) :
    CutoffDifferential.CM.Construction.cutoffGradientMultiply b g u = ∑ i,
      (cutoffGradientInsertion i).compLpL 2 volume (CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u) := by
  change LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) (CutoffDifferential.CM.Construction.cutoffGradientComponents b g u) = _
  simp only [LpComponents.CM.Construction.lpOrthonormalSynthesis, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.basisFun ι ℂ i)).compLpL 2 volume
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u)) = _
  exact Finset.sum_congr rfl (fun i _ => cutoffGradientInsertion_compLpL i _)

theorem cutoffGradientMultiply_operator_sum (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ)) :
    (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g).restrictScalars ℝ = ∑ i,
      ((cutoffGradientInsertion i).compLpL 2 (volume : Measure E)).comp
        ((CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) (∂_{b i} g : 𝓢(E, ℂ))).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    using cutoffGradientMultiply_sum b g u

theorem strongSobolev_cutoffGradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E))
    (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g u) := by
  rw [cutoffGradientMultiply_sum]
  apply StrongCutoffOperators.CM.Construction.strongSobolev_finset_sum b n Finset.univ
  intro i _
  exact StrongSobolevAdjoints.CM.Construction.strongSobolev_compLpL b (cutoffGradientInsertion i) n
    (StrongCutoffOperators.CM.Construction.strongSobolev_schwartz_multiply b n (∂_{b i} g : 𝓢(E, ℂ)) u hu)

theorem strongSobolev_cutoffGradient_adjoint (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (((CutoffDifferential.CM.Construction.cutoffGradientMultiply b g).restrictScalars ℝ).adjoint u) := by
  rw [cutoffGradientMultiply_operator_sum, map_sum, sum_apply]
  apply StrongCutoffOperators.CM.Construction.strongSobolev_finset_sum b n Finset.univ
  intro i _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  exact StrongCutoffOperators.CM.Construction.strongSobolev_schwartz_multiply_adjoint b n (∂_{b i} g : 𝓢(E, ℂ)) _
    (StrongSobolevAdjoints.CM.Construction.strongSobolev_compLpL_adjoint b (cutoffGradientInsertion i) n hu)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffGradient.CM.Construction
