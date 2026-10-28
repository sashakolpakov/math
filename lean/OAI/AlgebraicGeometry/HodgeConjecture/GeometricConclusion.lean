import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialCofinalModuli
import OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientComparison

/-! # Geometric Conclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricConclusion.CMExtractionIntrinsic

noncomputable section

/-! Geometric CMExtraction at every sufficiently divisible source level. The
source reference and normalized test precede all level and prime choices.
Only the identified complete upstream propositions remain inputs. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

def FullIsogenyQuotientGeometricComparisonConclusion
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E)
    (dref : Fin places.count → Bool) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin places.count × Fin 3) MpR MpF MpA) (base : ℕ)
    (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0}) : Prop :=
  ∃ (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count)
    (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom),
    P.b = B.b ∧ P.distinguished.val = 0 ∧
    (∀ i, P.embeddings i = HeckeCycles.ReferenceDatum.CM.embeddings E places (CMExtraction.InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places i)) ∧
    P.compactSigns = dref ∘ CMExtraction.InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places ∧
    ∃ R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W,
      ∃ N : ℕ, 3 ≤ N ∧ base ∣ N ∧ R.depth ∣ N ∧
        ∀ L : ℕ, 0 < L → N ∣ L →
          ∃ M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R,
            M.level = L ∧
            ∀ (excluded : Finset ℕ) (bound : ℕ),
              ∃ (q : ℕ) (hq : q.Prime),
                let : Fact q.Prime := ⟨hq⟩
                bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧
                PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.integral.base.extension.carrier q ∧
                IsogenyQuotientComparison.CMExtractionIntrinsic.FullRetainedPrimeComparisonConclusion E P hP hμ v hv W R M
                  (HeckeCycles.ReferenceDatum.CM.source_degree E places).1 (HeckeCycles.ReferenceDatum.CM.source_degree E places).2 hFiniteDescent q (CMExtraction.ParameterChoices.algebraicEmbedding E)

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricConclusion.CMExtractionIntrinsic
