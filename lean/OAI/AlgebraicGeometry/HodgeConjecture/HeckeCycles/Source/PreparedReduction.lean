import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SphericalOrdinaryReduction

/-! # Prepared Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PreparedReduction.CM

noncomputable section

/-! A compact proposition for the complete source-compatible ordinary
reduction conclusion, with its spherical input and local-frame bounds. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

universe u v

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
  {K : Type} [Field K] [NumberField K]
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
  (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
  (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
  (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
  {I : Type u} [Fintype I] (fields : I → Type v)
  [∀ i, Field (fields i)] [∀ i, NumberField (fields i)]
  (excluded : Finset ℕ) (bound : ℕ)

def Conclusion : Prop :=
    ∃ A : ℕ, 0 < A ∧
      (∀ (q : ℕ) [Fact q.Prime], A < q →
        (∀ (f : E →+* ℚ_[q]) (u : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q), u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q →
          FactorTheta.CM.action E L f (u, 1) φ = φ) ∧
        (∀ (τ : E →+* ℚ_[q]) (χ : NumberField.RingOfIntegers E →+* ℤ_[q]),
          (∀ a : NumberField.RingOfIntegers E, τ a = (χ a : ℚ_[q])) →
          Local.Lattice.CM.localLattice τ P.lattice = Local.Lattice.CM.standard (q := q))) ∧
      IntegralOrdinaryReduction.CM.Ordinary.Conclusion hTorsionQuotient E P iota κ N F fields excluded (max bound A)

theorem from_inputs
    (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput) (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0})
    (hIntegralModel : ArithmeticModels.CM.IntegralModelInput) (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v})
    (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0})
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hF : F.IsFine) (hball : F.HasProjectiveBallComponents κ) :
    Conclusion E L hTorsionQuotient P iota κ N F φ fields excluded bound :=
  SphericalOrdinaryReduction.CM.Ordinary.exists_reduction E L hAdelicTheta inputs hIntegralModel hNeighborCounting hFrobeniusKernel
    hCMPoints hCartierDuality hTorsionQuotient P iota κ N F hP hEmb hN hF hball φ fields excluded bound

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PreparedReduction.CM
