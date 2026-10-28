import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.BaseInvariance
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiberRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.JointMonicity

/-! # Kernel Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.KernelPair.IntegralAuxiliaryAction

noncomputable section

/-! The actual auxiliary relation is the kernel pair of a finite etale
prescribed-level classifying map. All relation witnesses are constructed
on its reduced pullback scheme and then give categorical maps on all tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem prescribed_map_kernelPair (hrigid : U.PrescribedRigid)
    (A : PEL.Has.IntegralPELObject P R iotaO N Y)
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ Y, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback f).data B.data))
    (q : X ⟶ Y) [IsFinite q.left] [Etale q.left]
    (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.forgetAuxiliary.data) :
    IsKernelPair q (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) := by
  let a := ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L
  let b := ActionSpace.IntegralAuxiliaryAction.target U hU
  have : JointlyMono₂ a b := JointMonicity.IntegralAuxiliaryAction.jointlyMono U hU hrigid
  have hsq := (IsPullback.of_hasPullback q q).map (Over.forget (Spec (.of R)))
  have : IsFinite (pullback.fst q q).left :=
    MorphismProperty.of_isPullback hsq.flip (inferInstanceAs (IsFinite q.left))
  have : Etale (pullback.fst q q).left :=
    MorphismProperty.of_isPullback hsq.flip (inferInstanceAs (Etale q.left))
  have : IsReduced (pullback q q).left := Finite.EtaleReduced.finite_etale_isReduced (pullback.fst q q).left
  have hab : a ≫ q = b ≫ q := BaseInvariance.IntegralAuxiliaryAction.prescribed_map_invariant U hU A hA q e
  let v : ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ pullback q q := pullback.lift a b hab
  obtain ⟨r, hra, hrb⟩ := FiberRelation.IntegralAuxiliaryAction.homRelation_of_equal_prescribed_map U hU A q e
    (pullback.fst q q) (pullback.snd q q) pullback.condition
  have hvr : v ≫ r = 𝟙 (ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L) := by
    apply JointlyMono₂.right_cancellation (p₁ := a) (p₂ := b)
    · rw [Category.assoc, hra, Category.id_comp]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, hrb, Category.id_comp]
      exact pullback.lift_snd _ _ _
  have hrv : r ≫ v = 𝟙 (pullback q q) := by
    apply pullback.hom_ext
    · change (r ≫ pullback.lift a b hab) ≫ pullback.fst q q = (𝟙 _) ≫ pullback.fst q q
      rw [Category.assoc, pullback.lift_fst, hra, Category.id_comp]
    · change (r ≫ pullback.lift a b hab) ≫ pullback.snd q q = (𝟙 _) ≫ pullback.snd q q
      rw [Category.assoc, pullback.lift_snd, hrb, Category.id_comp]
  exact IsPullback.of_iso_pullback ⟨hab⟩ ⟨v, r, hvr, hrv⟩
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.KernelPair.IntegralAuxiliaryAction
