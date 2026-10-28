import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.PairDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.MultiplicationRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf

/-! # Multiplication Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct multiplication on the actual arithmetic family quotient,
with its exact equation after the faithfully flat cover of fiber pairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_multiplication_descends (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (A : Over ((Over.pullback b).obj Q).left)
    (q : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left)
    (hcart : IsPullback ((Over.pullback b).map U.prescribedProjection).left q
      ((Over.pullback b).map π).left A.hom)
    (hq : IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) :
    ∃ q₂ : ((Over.pullback b).obj U.prescribedPairSpace).left ⟶ (A ⊗ A).left,
      q₂ ≫ (fst A A).left = ((Over.pullback b).map U.prescribedPairFst).left ≫ q ∧
      q₂ ≫ (snd A A).left = ((Over.pullback b).map U.prescribedPairSnd).left ≫ q ∧
      IsPullback ((Over.pullback b).map U.prescribedPairProjection).left q₂
        ((Over.pullback b).map π).left (A ⊗ A).hom ∧
      Flat q₂ ∧ Surjective q₂ ∧ LocallyOfFinitePresentation q₂ ∧
      ∃! m : A ⊗ A ⟶ A, q₂ ≫ m.left = ((Over.pullback b).map U.prescribedMul).left ≫ q := by
  let F := Over.pullback b
  obtain ⟨q₂, h₁, h₂, hc, hflat, hsurj, hfp, hpair⟩ := U.prescribed_pair_descends hU π hk b A q hcart hq
  have hs := congrArg (fun f => (F.map f).left) (U.prescribedMulOverlap_source π)
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedMulOverlap_target hU π hk hrigid)
  have hm : (F.map U.prescribedMul).left ≫ (F.map U.prescribedProjection).left =
      (F.map U.prescribedPairProjection).left := by
    rw [← Over.comp_left, ← F.map_comp, U.prescribedMul_projection]
  simp only [F.map_comp, Over.comp_left] at hs ht
  refine ⟨q₂, h₁, h₂, hc, hflat, hsurj, hfp, ?_⟩
  exact Family.QuotientOf.family_quotient_operation_descends (F.map π).left (F.map U.prescribedProjection).left
    (F.map U.prescribedPairProjection).left A (A ⊗ A) q q₂ hcart.w.symm hc.w.symm
    _ _ hq.w _ _ hpair (F.map U.prescribedMul).left hm (F.map (U.prescribedMulOverlap π)).left hs ht

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
