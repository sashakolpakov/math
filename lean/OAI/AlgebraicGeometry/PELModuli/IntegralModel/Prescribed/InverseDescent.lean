import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.InverseRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientEndomorphism

/-! # Inverse Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The inverse operation of the original universal abelian family
descends to the actual family quotient after arbitrary scalar change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_inverse_descends (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (A : Over ((Over.pullback b).obj Q).left)
    (q : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (hcart : IsPullback ((Over.pullback b).map U.prescribedProjection).left q
      ((Over.pullback b).map π).left A.hom)
    (hq : IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) :
    ∃! d : A ⟶ A, q ≫ d.left = ((Over.pullback b).map U.prescribedInverse).left ≫ q := by
  let F := Over.pullback b
  have hm : (F.map U.prescribedInverse).left ≫ (F.map U.prescribedProjection).left =
      (F.map U.prescribedProjection).left := by
    have h := congrArg (fun f => (F.map f).left) U.prescribedInverse_projection
    simpa only [F.map_comp, Over.comp_left] using h
  have hs : (F.map (U.prescribedInverseOverlap π)).left ≫
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left =
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left ≫ (F.map U.prescribedInverse).left := by
    have h := congrArg (fun f => (F.map f).left) (U.prescribedInverseOverlap_source π)
    simpa only [F.map_comp, Over.comp_left] using h
  have ht : (F.map (U.prescribedInverseOverlap π)).left ≫ (F.map (U.prescribedOverlapTarget hU π hk)).left =
      (F.map (U.prescribedOverlapTarget hU π hk)).left ≫ (F.map U.prescribedInverse).left := by
    have h := congrArg (fun f => (F.map f).left) (U.prescribedInverseOverlap_target hU π hk hrigid)
    simpa only [F.map_comp, Over.comp_left] using h
  exact Family.QuotientEndomorphism.family_quotient_endomorphism_descends (F.map π).left (F.map U.prescribedProjection).left
    A q hcart.w.symm _ _ hq (F.map U.prescribedInverse).left hm
    (F.map (U.prescribedInverseOverlap π)).left hs ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
