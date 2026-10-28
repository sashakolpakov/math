import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryPrime
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositeChoiceCompatibility
import OAI.RepresentationTheory.Hecke.IntrinsicParameters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeBounds
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity

/-! # Ordinary Setup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinarySetup.Intrinsic

noncomputable section

/-! A common prime for the retained theta test, integral model, and
full dense ordinary reduction. The comparison closures remain free to
be selected afterwards, so the native opposite place uses this same q. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositeChoiceCompatibility.ParameterChoices

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedClosureOrdinaryDensity.Ordinary

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPoints.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

theorem exists_retained_ordinary_setup
    (hOpenness : PELModuli.CMPoints.OrdinaryReduction.OpennessInput) (hSplitPrimes : PELModuli.CMPoints.Arithmetic.SplitPrimesInput)
    (hHilb : PELModuli.IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : PELModuli.IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : PELModuli.CMPoints.Descent.AbelianInput) (hCMAbelianVarietyM : PELModuli.CMPoints.Descent.ModuliInput)
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s : ℕ} (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
    (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
    (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (excluded : Finset ℕ) (bound : ℕ) :
    let Q := OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
    ∃ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      bound < q ∧ q ∉ excluded ∧ PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt E q ∧
      PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt M.integral.base.extension.carrier q ∧
      PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q ∧
      ∃ j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q,
      ∀ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
          ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver),
        let D := HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
        ∃ j : Q.QadicChoice q,
          j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE ∧
          j.iota = Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D ∧
          (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp (algebraMap E M.integral.base.extension.carrier) =
            LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (P.distinguished, true) ∧
          j.HasSplitCoordinates Q.extendedEmbedding ∧
          ∃ T : Q.GoodIntegralReduction q j, AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion T := by
  let Q := OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
  obtain ⟨q, hq, hb, hx, hE, hK, hgood, hchoices⟩ := OrdinaryPrime.Intrinsic.exists_retained_dense_ordinary_prime
    hOpenness hSplitPrimes hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM E hs hdegree P hP hμ v hv W R M excluded bound
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨j₀⟩ := hgood.qadic_choice hK
  refine ⟨q, hq, hb, hx, hE, hK, hgood, j₀, ?_⟩
  intro C
  let D := HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
  have hg := HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j₀ C
  have hqD := HeckeModel.Intrinsic.retainedHeckeModel_good_prime E P hP hμ v hv W R M j₀ C hgood
  obtain ⟨j, hc, hop, hfield, hsplit, T, ho, hrest⟩ :=
    hchoices (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D)
  have hj := OppositeChoiceCompatibility.ParameterChoices.opposite_choice_local_embedding E ιE D hg hμ hqD
    (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (fun x => RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding_spec ιE E.val.toRingHom x) j hop hfield
  exact ⟨j, hc, hop, hj, hsplit, T, ho, hrest⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinarySetup.Intrinsic
