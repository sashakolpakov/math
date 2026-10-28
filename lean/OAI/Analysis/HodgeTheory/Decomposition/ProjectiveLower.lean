import OAI.Analysis.HodgeTheory.Decomposition.CoefficientHodge
import OAI.Analysis.HodgeTheory.Decomposition.LocalFieldCutoff

/-! # Projective Lower -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLower.Constructions

noncomputable section

/-! The actual remaining lower-order Hodge coefficients define bounded
L² maps after a chart cutoff and preserve every natural Sobolev order. -/

open _root_.MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectiveHodgeValueGradientCutoffL2 :
    Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℂ]
      Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2 (stdOrthonormalBasis ℂ (GradientCoefficient.Constructions.ProjectiveGradientValues V n)) (EuclideanSpace.basisFun _ ℂ)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen η hη hηc hηU
    (CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient V e n) (CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient_smooth V e n he)

def projectiveHodgeValueValueCutoffL2 :
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℂ]
      Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2 (EuclideanSpace.basisFun _ ℂ) (EuclideanSpace.basisFun _ ℂ)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen η hη hηc hηU
    (CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient V e n) (CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient_smooth V e n he)

theorem projectiveHodgeValueGradientCutoffL2_coe
    (u : Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU u x =
        η x • CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient V e n x (u x) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_coe _ _ _ η hη hηc hηU _ (CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient_smooth V e n he)
    (fun x hx => CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient_complex_smul V e n he x hx) u

theorem projectiveHodgeValueValueCutoffL2_coe
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU u x =
        η x • CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient V e n x (u x) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_coe _ _ _ η hη hηc hηU _ (CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient_smooth V e n he)
    (fun x hx => CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient_complex_smul V e n he x hx) u

theorem projectiveHodgeValueGradientCutoffL2_memSobolev (s : ℕ)
    (u : Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hu : MemSobolev (s : ℝ) 2 (u : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n))) :
    MemSobolev (s : ℝ) 2
      (projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_memSobolev _ _ _ η hη hηc hηU _
    (CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient_smooth V e n he) s u hu

theorem projectiveHodgeValueValueCutoffL2_memSobolev (s : ℕ)
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hu : MemSobolev (s : ℝ) 2
      (u : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))) :
    MemSobolev (s : ℝ) 2
      (projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_memSobolev _ _ _ η hη hηc hηU _
    (CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient_smooth V e n he) s u hu

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLower.Constructions
