import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.JointMonicity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentedRelations

/-! # Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Relation.IntegralAuxiliaryAction

noncomputable section

/-! Construct the actual internal integral auxiliary equivalence
relation. Classification and rigidity are used only on reduced tests;
joint monicity holds on all schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

def equivalenceRelation (hrigid : U.PrescribedRigid) :
    CategoryTheory.EquivalenceRelation (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left := by
  have : JointlyMono₂ (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) := JointMonicity.IntegralAuxiliaryAction.jointlyMono U hU hrigid
  exact AbelianModuli.ReferenceFamily.RepresentedRelations.over_equivalenceRelation_left
    (Classical.choice (Reduced.RepresentedRelations.exists_equivalenceRelation_of_reduced_hom
      (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) (ActionPoints.IntegralAuxiliaryAction.homEquivalence U hU)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Relation.IntegralAuxiliaryAction
