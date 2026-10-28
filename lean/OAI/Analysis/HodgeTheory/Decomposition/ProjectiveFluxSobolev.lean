import OAI.Analysis.HodgeTheory.Decomposition.LocalFieldCutoff
import OAI.Analysis.HodgeTheory.Decomposition.CoefficientHodge
import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization

/-! # Projective Flux Sobolev -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFluxSobolev.Constructions

noncomputable section

/-! The actual lower-order Hodge flux, after a chart cutoff, is a genuine
bounded L² operator preserving every natural Sobolev order. -/

open _root_.MeasureTheory TemperedDistribution
open scoped ContDiff _root_.Manifold SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectiveHodgeFluxCutoffL2 :
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℂ]
    Lp (GradientCoefficient.Constructions.ProjectiveGradientValues V n) 2 (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2 (EuclideanSpace.basisFun _ ℂ) (stdOrthonormalBasis ℂ (GradientCoefficient.Constructions.ProjectiveGradientValues V n))
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen η hη hηc hηU
    (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n) (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient_smooth V e n he)

theorem projectiveHodgeFluxCutoffL2_coe
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    ∀ᵐ x ∂(volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU u x = η x • GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x (u x) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_coe _ _ _ η hη hηc hηU _ (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient_smooth V e n he)
    (fun x hx => CoefficientHodge.Constructions.projectiveHodgeFluxCoefficient_complex_smul V e n he x hx) u

theorem projectiveHodgeFluxCutoffL2_memSobolev (s : ℕ)
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hu : MemSobolev (s : ℝ) 2
      (u : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))) :
    MemSobolev (s : ℝ) 2
      (projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU u :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n)) :=
  LocalFieldCutoff.Constructions.localFieldCutoffL2_memSobolev _ _ _ η hη hηc hηU _
    (GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient_smooth V e n he) s u hu

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveHodgeFluxCutoffL2_energy_h1
    (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (hs : tsupport f ⊆ e.source)
    (hbound : ∃ B : ℝ, ∀ a, ‖VectorEnergyLocalization.Constructions.projectiveVectorH1Localization V e he (n + 1) f hf hs a‖ ≤
      B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    MemSobolev 1 2
      (projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU
        (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) :
          𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientCoefficient.Constructions.ProjectiveGradientValues V n)) := by
  let w : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) f hf hs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)
  have hw : MemSobolev 1 2
      (w : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) :=
    VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization_memSobolev V e he n f hf hs hbound u
  have hw' : MemSobolev ((1 : ℕ) : ℝ) 2
      (w : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
    simpa only [Nat.cast_one] using hw
  simpa only [Nat.cast_one] using
    projectiveHodgeFluxCutoffL2_memSobolev V e n he η hη hηc hηU 1 w hw'

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveFluxSobolev.Constructions
