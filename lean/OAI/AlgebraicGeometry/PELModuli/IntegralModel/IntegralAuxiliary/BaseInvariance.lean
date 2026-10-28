import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FamilyFibers

/-! # Base Invariance -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.BaseInvariance.IntegralAuxiliaryAction

noncomputable section

/-! Forgetting the auxiliary marking is invariant under the actual
auxiliary relation whenever the prescribed family is fine on reduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem prescribed_map_invariant (A : PEL.Has.IntegralPELObject P R iotaO N Y)
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ Y, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback f).data B.data))
    (q : X ⟶ Y) (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.forgetAuxiliary.data) :
    ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ q = ActionSpace.IntegralAuxiliaryAction.target U hU ≫ q := by
  let a := ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L
  let b := ActionSpace.IntegralAuxiliaryAction.target U hU
  let B := U.forgetAuxiliary.pullback a
  let es := IntegralPEL.FamilyFibers.prescribedFamilyPullbackComparison A U.forgetAuxiliary q e a
  let et := (IntegralPEL.FamilyFibers.prescribedFamilyPullbackComparison A U.forgetAuxiliary q e b).trans
    (U.auxiliaryRelabelAtComparison hU a (ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L _ (𝟙 _))).forgetAuxiliary
  obtain ⟨f, _, hf⟩ := hA (ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L) B
  exact (hf (a ≫ q) ⟨es⟩).trans (hf (b ≫ q) ⟨et⟩).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.BaseInvariance.IntegralAuxiliaryAction
