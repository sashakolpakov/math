import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FramedOrdinary

/-! # Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Prime.CM.Hecke

noncomputable section

/-! TateComparison's literal good-prime predicate for the PEL model assembled from
the same IntegralModel integral family and CMPoints reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models.CM

theorem good_prime_from_reduction
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E] (places : GeometricSource.CM.Places E)
    {K : Type} [Field K] [NumberField K]
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
    (iota : E →+* K) (κ : K →+* ℂ) (N : ℕ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
    (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N F.space F.universal B)
    (r : ℕ) (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)
    (q : ℕ) [Fact q.Prime]
    (j : (Ordinary.Models.CM.singletonModel P iota κ N F B V r D e).QadicChoice q)
    (R : (Ordinary.Models.CM.singletonModel P iota κ N F B V r D e).GoodIntegralReduction q j)
    (hsplit : j.HasSplitCoordinates
      (Ordinary.Models.CM.singletonModel P iota κ N F B V r D e).extendedEmbedding)
    (C : AbelianScheme.TateComparison.Local.IntegralType places.count →
      AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback B.generic).obj V.toOver)) :
    (Models.CM.Hecke.data V D e C
      (PairedCompletion.CM.pairedCharacter E j ((algebraMap K B.extension.carrier).comp iota) places)).IsGoodCompletelySplitPrime := by
  exact GoodPrime.CM.good_prime_conditions E
    (Ordinary.Models.CM.singletonModel P iota κ N F B V r D e) j R places hsplit (0 : Fin 1)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Prime.CM.Hecke
