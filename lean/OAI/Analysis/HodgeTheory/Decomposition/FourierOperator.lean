import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Fourier Operator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FourierOperator.Constructions

noncomputable section

/-! Fourier symbols of genuine constant-coefficient first-order operators
on vector-valued Schwartz functions. -/

open FourierTransform LineDeriv _root_.MeasureTheory
open scoped SchwartzMap BigOperators

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [Fintype ι]

theorem fourier_postcomp_schwartz (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    𝓕 (SchwartzMap.postcompCLM L f) = SchwartzMap.postcompCLM L (𝓕 f) := by
  ext ξ
  change 𝓕 (fun x => L (f x)) ξ = L (𝓕 (f : E → F) ξ)
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff (μ := volume) (f := (f : E → F)) ξ).mpr f.integrable
  simp only [Circle.smul_def] at hi ⊢
  simp_rw [← map_smul]
  exact L.integral_comp_comm hi

def schwartzFirstOrder (directions : ι → E) (symbol : ι → F →L[ℂ] G) :
    𝓢(E, F) →L[ℂ] 𝓢(E, G) :=
  ∑ i, (SchwartzMap.postcompCLM (symbol i)).comp (lineDerivOpCLM ℂ 𝓢(E, F) (directions i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [CompleteSpace G] in
theorem schwartzFirstOrder_apply (directions : ι → E) (symbol : ι → F →L[ℂ] G)
    (f : 𝓢(E, F)) (x : E) :
    schwartzFirstOrder directions symbol f x = ∑ i, symbol i (fderiv ℝ (f : E → F) x (directions i)) := by
  simp only [schwartzFirstOrder, sum_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.postcompCLM_apply, lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The Fourier transform of the actual derivative is multiplication by its linear symbol. -/
theorem schwartzFirstOrder_fourier (directions : ι → E) (symbol : ι → F →L[ℂ] G)
    (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (schwartzFirstOrder directions symbol f) ξ =
      (2 * Real.pi * Complex.I) •
        ∑ i, (inner ℝ ξ (directions i)) • symbol i (𝓕 f ξ) := by
  simp only [schwartzFirstOrder, sum_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    fourier_sum, fourier_postcomp_schwartz, SchwartzMap.fourier_lineDerivOp_eq,
    SchwartzMap.postcompCLM_apply, smul_apply,
    map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have htemp : (fun x : E => inner ℝ x (directions i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (directions i)).hasTemperateGrowth
  rw [SchwartzMap.smulLeftCLM_apply htemp]
  change (2 * Real.pi * Complex.I) • symbol i ((inner ℝ ξ (directions i)) • (𝓕 f ξ)) = _
  exact congrArg (fun y : G => (2 * Real.pi * Complex.I) • y)
    (((symbol i).restrictScalars ℝ).map_smul (inner ℝ ξ (directions i)) (𝓕 f ξ))

end

end OAI.Analysis.HodgeTheory.Decomposition.FourierOperator.Constructions
