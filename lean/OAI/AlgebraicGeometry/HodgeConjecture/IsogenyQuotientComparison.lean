import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Correspondences
import OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparisonConclusion

/-! # Isogeny Quotient Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientComparison.CMExtractionIntrinsic

noncomputable section

/-! Discharge the old conditional extraction premise using the complete
native IsogenyQuotient proposition. The original five-clause extraction conclusion
is retained verbatim for the constructed correspondence on the same model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Matrix

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0}) (q : ℕ) [Fact q.Prime]

def FullRetainedPrimeComparisonConclusion (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) : Prop :=
  ∃ hgood : CMExtraction.PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q,
  ∃ j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q,
  ∃ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.model.space,
    CMExtraction.IsogenyQuotient.Correspondences.Intrinsic.RetainedNativeFullWitnesses E P hP hμ v hv W R M hs hdegree hgood j₀ hFiniteDescent C ∧
    CMExtraction.IsogenyQuotient.Correspondences.Intrinsic.RetainedFullRawMultisets E P hP hμ v hv W R M hs hdegree hgood j₀ hFiniteDescent C ∧
    (CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀
      (fun t => CMExtraction.IsogenyQuotient.Correspondence.retainedFineCorrespondence M.integral (C t))).RealizesIsogenyQuotient ∧
    ModelComparisonConclusion.CMExtractionIntrinsic.RetainedModelComparisonConclusion E P hP hμ v hv W R M j₀
      (fun t => CMExtraction.IsogenyQuotient.Correspondence.retainedFineCorrespondence M.integral (C t)) CMExtraction.Theta.verifiedHodgeDecomposition ιE

theorem fullIsogenyQuotient_retained_comparison (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (hIsogenyQuotient : CMExtraction.IsogenyQuotient.Transport.CompleteIsogenyQuotientTransportInput)
    (hold : PrimeComparisonConclusion.CMExtractionIntrinsic.RetainedPrimeComparisonConclusion E P hP hμ v hv W R M ιE q) :
    FullRetainedPrimeComparisonConclusion E P hP hμ v hv W R M hs hdegree hFiniteDescent q ιE := by
  obtain ⟨hgood, j₀, hextract⟩ := hold
  obtain ⟨C, hwitness, hraw, hrealizes⟩ :=
    CMExtraction.IsogenyQuotient.Correspondences.Intrinsic.fullIsogenyQuotient_retained_correspondences E P hP hμ v hv W R M hs hdegree hgood j₀ hFiniteDescent hIsogenyQuotient
  exact ⟨hgood, j₀, C, hwitness, hraw, hrealizes, hextract _ hrealizes⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.IsogenyQuotientComparison.CMExtractionIntrinsic
