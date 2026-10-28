import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientProduct

/-! # Poincare Quotient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual dual and abelian quotients construct their product
quotient, with the prescribed Poincare relation as its exact kernel pair. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_poincare_product_quotient {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (D A : Over ((Over.pullback b).obj Q).left)
    (qd : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ D.left)
    (qa : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left)
    (hd : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left qd
      ((Over.pullback b).map π).left D.hom)
    (ha : IsPullback ((Over.pullback b).map U.prescribedProjection).left qa
      ((Over.pullback b).map π).left A.hom)
    (hqd : IsKernelPair qd ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left)
    (hqa : IsKernelPair qa ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) :
    ∃ q : ((Over.pullback b).obj U.prescribedPoincareSpace).left ⟶ (D ⊗ A).left,
      q ≫ (fst D A).left = ((Over.pullback b).map U.prescribedPoincareDual).left ≫ qd ∧
      q ≫ (snd D A).left = ((Over.pullback b).map U.prescribedPoincareAbelian).left ≫ qa ∧
      IsPullback ((Over.pullback b).map U.prescribedPoincareProjection).left q
        ((Over.pullback b).map π).left (D ⊗ A).hom ∧
      IsFinite q ∧ Etale q ∧ Surjective q ∧
      IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left := by
  let F := Over.pullback b
  have hp : IsPullback (F.map U.prescribedPoincareDual).left (F.map U.prescribedPoincareAbelian).left
      (F.map U.prescribedDualProjection).left (F.map U.prescribedProjection).left :=
    (U.prescribedPoincare_square.map F).map (Over.forget S)
  obtain ⟨q, h₁, h₂, hc⟩ := Family.QuotientProduct.family_quotient_product_cartesian (F.map π).left
    (F.map U.prescribedDualProjection).left (F.map U.prescribedProjection).left D A qd qa hd ha _ _ hp
  have hap : (F.map U.prescribedPoincareDual).left ≫ (F.map U.prescribedDualProjection).left =
      (F.map U.prescribedPoincareProjection).left := by
    rw [← Over.comp_left, ← F.map_comp]
  rw [hap] at hc
  have : IsFinite (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (IsFinite π.left))
  have : Etale (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Etale π.left))
  have : Surjective (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Surjective π.left))
  have hf : IsFinite q := MorphismProperty.of_isPullback hc (inferInstanceAs (IsFinite (F.map π).left))
  have het : Etale q := MorphismProperty.of_isPullback hc (inferInstanceAs (Etale (F.map π).left))
  have hsur : Surjective q := MorphismProperty.of_isPullback hc (inferInstanceAs (Surjective (F.map π).left))
  have hs₁ := congrArg (fun m => (F.map m).left) (U.prescribedPoincareOverlapDual_source π)
  have hs₂ := congrArg (fun m => (F.map m).left) (U.prescribedPoincareOverlapAbelian_source π)
  have ht₁ := congrArg (fun m => (F.map m).left) (U.prescribedPoincareTarget_dual π hU hk)
  have ht₂ := congrArg (fun m => (F.map m).left) (U.prescribedPoincareTarget_abelian π hU hk)
  simp only [F.map_comp, Over.comp_left] at hs₁ hs₂ ht₁ ht₂
  have he := Family.QuotientProduct.family_quotient_product_coequalizes D A qd qa q _ _ h₁ h₂
    _ _ _ _ hqd.w hqa.w _ _ _ _ hs₁ hs₂ ht₁ ht₂
  have hsource : IsPullback (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection)).left
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left (F.map π).left
      ((F.map U.prescribedPoincareProjection).left ≫ (F.map π).left) := by
    have h := (((IsPullback.of_hasPullback (U.prescribedPoincareProjection ≫ π) π).flip).map F).map
      (Over.forget S)
    change IsPullback _ _ _ (F.map (U.prescribedPoincareProjection ≫ π)).left at h
    rw [F.map_comp, Over.comp_left] at h
    exact h
  have ht : (F.map (U.prescribedPoincareTarget π hU hk)).left ≫
      (F.map U.prescribedPoincareProjection).left =
        (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection)).left := by
    rw [← Over.comp_left, ← F.map_comp, U.prescribedPoincareTarget_projection]
  exact ⟨q, h₁, h₂, hc, hf, het, hsur, Family.QuotientOf.kernelPair_of_cartesian_relation _ _ _ _ hc _ _ _ hsource ht he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
