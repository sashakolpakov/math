import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionPointTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle

/-! # Action Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every coefficient endomorphism preserves the actual prescribed
abelian descent relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedActionOverlap_target (hrigid : U.PrescribedRigid) (r : NumberField.RingOfIntegers E) :
    U.prescribedActionOverlap π r ≫ U.prescribedOverlapTarget hU π hk =
      U.prescribedOverlapTarget hU π hk ≫ U.prescribedAction r := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedActionOverlap π r
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hf : k ≫ f = f := by
    change k ≫ src ≫ a = src ≫ a
    rw [← Category.assoc, U.prescribedActionOverlap_source, Category.assoc, U.prescribedAction_projection]
  have hg : k ≫ g = g := U.prescribedActionOverlap_base π r
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hy : (src.left ≫ (U.prescribedAction r).left) ≫
      U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left := by
    change (src.left ≫ (U.prescribedAction r).left) ≫ a.left = f.left
    rw [Category.assoc, ← Over.comp_left, U.prescribedAction_projection]
    rfl
  have hpoints := U.prescribedPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f g
    (by simpa only [Category.assoc] using congrArg (fun z => k ≫ z) h) h hf hg
    (k.left ≫ src.left) (src.left ≫ (U.prescribedAction r).left) rfl hy
    (congrArg Over.Hom.left (U.prescribedActionOverlap_source π r))
  have hp := U.prescribedPointTransport_action hU π hk r f g h src.left rfl
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hp.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
