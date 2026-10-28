import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryLabels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel

/-! # Ordinary Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryCharacters.Intrinsic

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

theorem retained_field_embedding (w : Fin s × Bool) :
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C) w =
      ((HeckeCycles.QadicModelMap.CM.localFieldEmbedding j₀).comp (algebraMap E M.integral.base.extension.carrier)).comp
        (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E)
  intro a
  rw [LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers]
  exact RingHom.congr_fun j₀.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom
      ((algebraMap E M.integral.base.extension.carrier).comp
        (HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w).toRingHom) a)

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (hj : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp (algebraMap E M.integral.base.extension.carrier) =
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C) (P.distinguished, true))

include hj in
theorem retained_opposite_local_characters (w : Fin s × Bool) :
    j.localCharacter (algebraMap E M.integral.base.extension.carrier)
      (OrdinaryLabels.Intrinsic.retainedOrdinaryLabels E P hP hμ w) =
      (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C).localCharacter w := by
  apply OrdinaryLabels.Intrinsic.retainedOrdinaryLabels_character E P hP hμ j₀ j
    (algebraMap E M.integral.base.extension.carrier)
  have hp := retained_field_embedding E P hP hμ v hv W R M j₀ C (P.distinguished, true)
  have hlabel : HeckeCycles.PairedCompletion.CM.placeIndex E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) (P.distinguished, true) = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
    change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P P.distinguished = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    rw [Multiplicity.Period.nativeArchLabel_active E P hμ, mul_one]
  exact hj.trans (hp.trans (congrArg
    (fun τ : Gal(E/ℚ) =>
      ((HeckeCycles.QadicModelMap.CM.localFieldEmbedding j₀).comp (algebraMap E M.integral.base.extension.carrier)).comp
        τ.toRingHom) hlabel))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryCharacters.Intrinsic
