import OAI.AlgebraicGeometry.HodgeConjecture.ModelComparisonConclusion
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Theta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices

/-! # Prime Comparison Conclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparisonConclusion.CMExtractionIntrinsic

noncomputable section

/-! Choose one good split prime for the fixed model and normalized test,
then extract the CM classes from its full geometric correspondences. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)

def RetainedPrimeComparisonConclusion (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (q : ℕ) [Fact q.Prime] : Prop :=
  CMExtraction.PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q ∧
  ∃ j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q,
    ∀ C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
        ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver),
      (CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C).RealizesIsogenyQuotient →
        ModelComparisonConclusion.CMExtractionIntrinsic.RetainedModelComparisonConclusion E P hP hμ v hv W R M j₀ C CMExtraction.Theta.verifiedHodgeDecomposition ιE

end

end OAI.AlgebraicGeometry.HodgeConjecture.PrimeComparisonConclusion.CMExtractionIntrinsic
