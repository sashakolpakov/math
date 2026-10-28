import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PairRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientPairRelation

/-! # Pair Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual relative square of the scalar-changed family descends
to the relative square of the constructed family quotient. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_pair_descends
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
      IsKernelPair q₂ ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection)).left
        ((Over.pullback b).map (U.prescribedPairTarget π hU hk)).left := by
  let F := Over.pullback b
  have hp : IsPullback (F.map U.prescribedPairFst).left (F.map U.prescribedPairSnd).left
      (F.map U.prescribedProjection).left (F.map U.prescribedProjection).left :=
    (U.prescribedPair_square.map F).map (Over.forget S)
  obtain ⟨q₂, h₁, h₂, hc⟩ := Family.QuotientOf.family_quotient_pair_cartesian (F.map π).left
    (F.map U.prescribedProjection).left A q hcart _ _ hp
  have hap : (F.map U.prescribedPairFst).left ≫ (F.map U.prescribedProjection).left =
      (F.map U.prescribedPairProjection).left := by
    rw [← Over.comp_left, ← F.map_comp]
  rw [hap] at hc
  have : Flat (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Flat π.left))
  have : Surjective (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Surjective π.left))
  have : LocallyOfFinitePresentation (F.map π).left := MorphismProperty.of_isPullback
    (Specialization.base_change_square b π) (inferInstanceAs (LocallyOfFinitePresentation π.left))
  refine ⟨q₂, h₁, h₂, hc, MorphismProperty.of_isPullback hc (inferInstanceAs (Flat (F.map π).left)),
    MorphismProperty.of_isPullback hc (inferInstanceAs (Surjective (F.map π).left)),
    MorphismProperty.of_isPullback hc (inferInstanceAs (LocallyOfFinitePresentation (F.map π).left)), ?_⟩
  have hs₁ := congrArg (fun f => (F.map f).left) (U.prescribedPairOverlapFst_source π)
  have hs₂ := congrArg (fun f => (F.map f).left) (U.prescribedPairOverlapSnd_source π)
  have ht₁ := congrArg (fun f => (F.map f).left) (U.prescribedPairTarget_fst π hU hk)
  have ht₂ := congrArg (fun f => (F.map f).left) (U.prescribedPairTarget_snd π hU hk)
  simp only [F.map_comp, Over.comp_left] at hs₁ hs₂ ht₁ ht₂
  have heq := Family.QuotientPairRelation.family_quotient_pair_coequalizes A q q₂ _ _ h₁ h₂ _ _ hq.w _ _ _ _ hs₁ hs₂ ht₁ ht₂
  have hsource : IsPullback (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedPairProjection)).left
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection)).left (F.map π).left
      ((F.map U.prescribedPairProjection).left ≫ (F.map π).left) := by
    have h := (((IsPullback.of_hasPullback (U.prescribedPairProjection ≫ π) π).flip).map F).map (Over.forget S)
    change IsPullback _ _ _ (F.map (U.prescribedPairProjection ≫ π)).left at h
    rw [F.map_comp, Over.comp_left] at h
    exact h
  have ht := congrArg (fun f => (F.map f).left) (U.prescribedPairTarget_projection π hU hk)
  simp only [F.map_comp, Over.comp_left] at ht
  rw [hap] at ht
  exact Family.QuotientOf.kernelPair_of_cartesian_relation (F.map π).left (F.map U.prescribedPairProjection).left
    (A ⊗ A).hom q₂ hc _ _ _ hsource ht heq

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
