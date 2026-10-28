import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily

/-! # PEL Reconstruction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELReconstruction.CM

noncomputable section

/-! Recover the native IntegralModel PEL object from a TateComparison family in the PEL
locus. This is used on arbitrary reduced test schemes in classification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELFamily.CM.Family

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {g N : ℕ} {δ : Fin g → ℕ} {S : Scheme}

def toActionData (D : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (h : D.IsPEL δ (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom) :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S where
  polarized := D.toPolarized h
  action := AbelianScheme.TateComparison.PELAdapters.actionFromEnd D.action

theorem ofActionData_toActionData
    (D : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (h : D.IsPEL δ (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom) :
    PELFamily.CM.Family.ofActionData (toActionData D h) = D := by
  change AbelianScheme.TateComparison.PEL.PELFamilyData.mk D.abelian D.dual D.polarizationMap D.marking
    (AbelianScheme.TateComparison.PELAdapters.actionToEnd (AbelianScheme.TateComparison.PELAdapters.actionFromEnd D.action)) = D
  rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_fromEnd]

variable {R : Type} [CommRing R] {iotaO : NumberField.RingOfIntegers E →+* R}
  {X : Over (Spec (.of R))} {s : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}

def toIntegralObject
    (D : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N X.left)
    (h : AbelianScheme.TateComparison.PELModuli.IsPELFamily P (X.hom.appTop.hom.comp (PELFamily.CM.Family.baseAction iotaO)) D) :
    PELModuli.IntegralModel.PEL.Has.IntegralPELObject P R iotaO N X where
  data := toActionData D h.1
  rosati := by
    apply (AbelianScheme.TateComparison.PELAdapters.rosati_iff (toActionData D h.1).polarized (toActionData D h.1).action).mp
    change (PELFamily.CM.Family.ofActionData (toActionData D h.1)).IsRosatiCompatible _
    rw [ofActionData_toActionData]
    exact h.1.2.2
  lieRanks := by
    apply (PELFamily.CM.Family.lie_signature_iff (toActionData D h.1)).mp
    rw [ofActionData_toActionData]
    exact h.2

theorem reconstructed_family
    (D : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N X.left)
    (h : AbelianScheme.TateComparison.PELModuli.IsPELFamily P (X.hom.appTop.hom.comp (PELFamily.CM.Family.baseAction iotaO)) D) :
    PELFamily.CM.Family.ofActionData (toIntegralObject D h).data = D :=
  ofActionData_toActionData D h.1

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELReconstruction.CM
