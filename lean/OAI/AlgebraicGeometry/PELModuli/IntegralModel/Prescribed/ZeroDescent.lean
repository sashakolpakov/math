import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.ZeroRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseChangedKernelPair

/-! # Zero Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct the zero section of the actual arithmetic family quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_zero_descends (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (A : Over ((Over.pullback b).obj Q).left)
    (q : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left)
    (hcart : IsPullback ((Over.pullback b).map U.prescribedProjection).left q
      ((Over.pullback b).map π).left A.hom)
    (hq : IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) :
    ∃! z : Over.mk (𝟙 ((Over.pullback b).obj Q).left) ⟶ A,
      ((Over.pullback b).map π).left ≫ z.left = ((Over.pullback b).map U.prescribedZero).left ≫ q := by
  let F := Over.pullback b
  have : Flat (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Flat π.left))
  have : Surjective (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Surjective π.left))
  have : LocallyOfFinitePresentation (F.map π).left := MorphismProperty.of_isPullback
    (Specialization.base_change_square b π) (inferInstanceAs (LocallyOfFinitePresentation π.left))
  have hz : (F.map U.prescribedZero).left ≫ (F.map U.prescribedProjection).left = 𝟙 _ := by
    have h := congrArg (fun f => (F.map f).left) U.prescribedZero_projection
    simpa only [F.map_comp, F.map_id, Over.comp_left, Over.id_left] using h
  have hs := congrArg (fun f => (F.map f).left) (U.prescribedZeroOverlap_source hU π hk)
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedZeroOverlap_target hU π hk hrigid)
  simp only [F.map_comp, Over.comp_left] at hs ht
  exact Family.QuotientOf.family_quotient_section_descends (F.map π).left (F.map U.prescribedProjection).left
    A q hcart.w.symm _ _ (BaseChangedKernelPair.over_baseChanged_kernelPair b π _ _ hk) _ _ hq.w
    (F.map U.prescribedZero).left hz (F.map (U.prescribedZeroOverlap hU π hk)).left hs ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
