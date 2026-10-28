import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource

/-! # Ordinary Hecke Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel.Intrinsic

noncomputable section

/-! The ordinary reduction at the opposite place uses the same retained
local characters and the identical IntegralModel Hecke model. -/

open scoped Classical
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

def retainedOrdinaryIndex : (OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M).Family :=
  ⟨0, by change (0 : ℕ) < 1; decide⟩

local notation "a₀" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel.Intrinsic.retainedOrdinaryIndex E P hP hμ v hv W R M

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (hj : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp (algebraMap E M.integral.base.extension.carrier) =
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C) (P.distinguished, true))

include hj in
theorem retained_ordinary_hecke_model_eq :
    HeckeCycles.Witt.PELSource.CM.heckeData (OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M) a₀ C
      (fun w => j.localCharacter (OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M).extendedEmbedding
        (OrdinaryLabels.Intrinsic.retainedOrdinaryLabels E P hP hμ w)) =
      HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C := by
  have he : (fun w => j.localCharacter
      (OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M).extendedEmbedding
      (OrdinaryLabels.Intrinsic.retainedOrdinaryLabels E P hP hμ w)) =
      (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C).localCharacter := by
    funext w
    exact OrdinaryCharacters.Intrinsic.retained_opposite_local_characters E P hP hμ v hv W R M j₀ C j hj w
  exact congrArg (M.integral.heckeData C) he

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel.Intrinsic
