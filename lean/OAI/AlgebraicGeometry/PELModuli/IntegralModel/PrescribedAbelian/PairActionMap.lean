import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientEndomorphism

/-! # Pair Action Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Each original coefficient endomorphism descends uniquely to the
actual arithmetic abelian quotient with its exact covering equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

include hrigid in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.exists_actionMap (r : NumberField.RingOfIntegers E) :
    ∃! m : B.abelian.scheme ⟶ B.abelian.scheme,
      B.abelianCover ≫ m.left = ((Over.pullback b).map (U.prescribedAction r)).left ≫ B.abelianCover := by
  let F := Over.pullback b
  have hm : (F.map (U.prescribedAction r)).left ≫ (F.map U.prescribedProjection).left =
      (F.map U.prescribedProjection).left := by
    have h := congrArg (fun f => (F.map f).left) (U.prescribedAction_projection r)
    simpa only [F.map_comp, Over.comp_left] using h
  have hs := congrArg (fun f => (F.map f).left) (U.prescribedActionOverlap_source π r)
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedActionOverlap_target hU π hk hrigid r)
  simp only [F.map_comp, Over.comp_left] at hs ht
  exact Family.QuotientEndomorphism.family_quotient_endomorphism_descends (F.map π).left (F.map U.prescribedProjection).left
    B.abelian.scheme B.abelianCover B.abelianCartesian.w.symm _ _ B.abelianKernelPair
    (F.map (U.prescribedAction r)).left hm (F.map (U.prescribedActionOverlap π r)).left hs ht

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.actionMap (r : NumberField.RingOfIntegers E) : B.abelian.scheme ⟶ B.abelian.scheme :=
  (B.exists_actionMap hrigid r).exists.choose

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.actionMap_cover (r : NumberField.RingOfIntegers E) :
    B.abelianCover ≫ (B.actionMap hrigid r).left =
      ((Over.pullback b).map (U.prescribedAction r)).left ≫ B.abelianCover :=
  (B.exists_actionMap hrigid r).exists.choose_spec

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
