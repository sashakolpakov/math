import OAI.Analysis.HodgeTheory.Decomposition.LocalFlux
import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongGradient

/-! # Forcing Regularity -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ForcingRegularity.Constructions

noncomputable section

/-! The actual local Hodge forcing has the derivative order needed for
each elliptic bootstrap step; its flux has one additional order. -/

open _root_.MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projectiveLocalHodgeForcing_memSobolev (s : ℕ)
    (u f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hu : MemSobolev ((s : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))))
    (hf : MemSobolev (s : ℝ) 2
      (f : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))) :
    MemSobolev (s : ℝ) 2
      (LocalFlux.Constructions.projectiveLocalHodgeForcing V e n he η hη hηc hηU u f :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  let b := stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let Ju := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u
  let Du := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) b u
  have hDu : MemSobolev (s : ℝ) 2 (Du : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n)) :=
    (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b s Du).mp (VectorStrongGradient.Constructions.vectorStrongSobolev_gradient_of_memSobolev b s u hu)
  have hJu : MemSobolev (s : ℝ) 2
      (Ju : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :=
    hu.mono (by linarith)
  have hC := ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2_memSobolev V e n he η hη hηc hηU s Du hDu
  have hE := ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2_memSobolev V e n he η hη hηc hηU s Ju hJu
  apply (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b s _).mp
  have hF := (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b s f).mpr hf
  have hCs := (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b s _).mpr hC
  have hEs := (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b s _).mpr hE
  simpa only [LocalFlux.Constructions.projectiveLocalHodgeForcing, sub_eq_add_neg] using
    (hF.add b s (hCs.neg b s)).add b s (hEs.neg b s)

theorem projectiveLocalHodgeFlux_memSobolev (s : ℕ)
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hu : MemSobolev ((s : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))) :
    MemSobolev ((s : ℝ) + 1) 2
      (LocalFlux.Constructions.projectiveLocalHodgeFlux V e n he η hη hηc hηU u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n)) := by
  let b := stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let Ju := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u
  have hJu : MemSobolev ((s + 1 : ℕ) : ℝ) 2
      (Ju : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
    simpa only [Nat.cast_succ] using hu
  have hF := ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2_memSobolev V e n he η hη hηc hηU (s + 1) Ju hJu
  have hFs := (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b (s + 1) _).mpr hF
  have hneg := (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b (s + 1) _).mp (hFs.neg b (s + 1))
  simpa only [LocalFlux.Constructions.projectiveLocalHodgeFlux, Nat.cast_succ] using hneg

end

end OAI.Analysis.HodgeTheory.Decomposition.ForcingRegularity.Constructions
