import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPackage
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledLocalFrames

/-! # Integral Ordinary Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralOrdinaryReduction.CM.Ordinary

noncomputable section

/-! Construct the arithmetic Albanese geometry and the full ordinary
quotient reduction data and local frames on the same integral PEL spread. Every geometric
and reduction property is obtained from complete named prerequisites. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites

universe u v

def Conclusion
    (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    {K : Type} [Field K] [NumberField K] {s : ℕ}
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    {I : Type u} [Fintype I] (L : I → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) : Prop :=
    ∃ (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
      (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N F.space F.universal B)
      (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver),
      let Q := Ordinary.Models.CM.singletonModel P iota κ N F B V r D e
      ∃ hQ : Q.HasPrescribedBallPeriods,
        (∀ (q : ℕ) [Fact q.Prime]
          (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback B.generic).obj V.toOver))
          (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q]),
          (Models.CM.Hecke.data V D e C χ).HasIntegralModelGeometry) ∧
        ∃ d : ℕ, bound ≤ d ∧ LabeledLocalFrames.CM.FramesAbove Q d ∧
          Constructed.OrdinaryPrime.CM.Ordinary.Conclusion hTorsionQuotient E K Q hQ L excluded d

theorem integral_and_native_reductions
    (hIntegralModel : ArithmeticModels.CM.IntegralModelInput)
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v})
    (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    {K : Type} [Field K] [NumberField K] {s : ℕ}
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hF : F.IsFine) (hball : F.HasProjectiveBallComponents κ)
    {I : Type u} [Fintype I] (L : I → Type v)
    [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    Conclusion hTorsionQuotient E P iota κ N F L excluded bound := by
  obtain ⟨B, hunit, V, hclassifies, hsmooth, hproper, hprojective,
    r, D, e, hcomponents, hbetti, hgeneration⟩ :=
    hIntegralModel s hs hdegree P hP iota κ hEmb N hN F hF
  let Q := Ordinary.Models.CM.singletonModel P iota κ N F B V r D e
  have hQ : Q.HasPrescribedBallPeriods := by
    refine ⟨hs, hdegree, fun _ => ?_⟩
    exact ⟨hP, hEmb, hN, hF, hball, hclassifies, hsmooth, hproper, hprojective,
      fun j => ⟨(hcomponents j).1, (hcomponents j).2.1,
        (hcomponents j).2.2.1, (hcomponents j).2.2.2.1⟩⟩
  refine ⟨B, V, r, D, e, hQ, ?_, ?_⟩
  · intro q _ C χ
    exact Models.CM.Hecke.geometry_from_integral V D e C χ hP hEmb hN.1 hunit
      hclassifies hsmooth hproper hprojective hcomponents hbetti hgeneration
  · exact LabeledLocalFrames.CM.native_reductions_with_frames Q hQ
      hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient L excluded bound

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralOrdinaryReduction.CM.Ordinary
