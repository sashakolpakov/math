import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Moduli
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models

/-! # Ordinary Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel.Intrinsic

noncomputable section

/-! CMPoints is applied to the very same integral family and component
schemes retained before the prime, with its period hypotheses proved. -/

open scoped Classical _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)

def retainedOrdinaryModel : PELModuli.CMPoints.Models.RankThreePELModel E E where
  s := s
  familyCount := 1
  iota := RingHom.id E
  complexEmbedding := E.val.toRingHom
  arithmetic := M.integral.base
  datum := fun _ => P
  level := fun _ => M.level
  moduli := fun _ => M.model
  integral := fun _ => M.integral.spread
  componentCount := fun _ => M.integral.count
  components := fun _ => M.integral.components
  decomposition := fun _ => M.integral.decomposition

theorem retainedOrdinaryModel_periods (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    (retainedOrdinaryModel E P hP hμ v hv W R M).HasPrescribedBallPeriods := by
  refine ⟨hs, hdegree, fun _ => ?_⟩
  refine ⟨hP, ?_, M.deep, M.fine, M.ballComponents, M.integral.classifies,
    M.integral.smooth, M.integral.proper, M.integral.projective, ?_⟩
  · change E.val.toRingHom.comp (RingHom.id E) = P.μ
    simpa only [RingHom.comp_id] using hμ.symm
  · intro i
    exact ⟨(M.integral.geometry i).1, (M.integral.geometry i).2.1,
      (M.integral.geometry i).2.2.1, (M.integral.geometry i).2.2.2.1⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel.Intrinsic
