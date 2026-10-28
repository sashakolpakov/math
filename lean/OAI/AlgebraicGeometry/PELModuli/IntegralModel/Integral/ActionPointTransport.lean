import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PointTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointMorphismTransport

/-! # Action Point Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every actual coefficient endomorphism of the prescribed integral
action commutes with the constructed point transport. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T W : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPointTransport_action (r : NumberField.RingOfIntegers E) [IsReduced T.left]
    (f g : T ⟶ X) (h : f ≫ π = g ≫ π)
    (x : T.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme.left)
    (hx : x ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = f.left) :
    U.prescribedPointTransport hU π hk f g h x hx ≫ (U.forgetAuxiliary.data.action.map r).left =
    U.prescribedPointTransport hU π hk f g h (x ≫ (U.forgetAuxiliary.data.action.map r).left)
      (by rw [Category.assoc, (U.forgetAuxiliary.data.action.map r).w]; exact hx) :=
  Family.PointMorphismTransport.FamilyPointTransport.transport_map U.forgetAuxiliary.data.polarized.abelian.scheme
    U.forgetAuxiliary.data.polarized.abelian.scheme (U.forgetAuxiliary.data.action.map r) f.left g.left
    (U.prescribedTransport hU π hk f g h).polarized.abelian
    (U.prescribedTransport hU π hk f g h).polarized.abelian
    ((U.prescribedTransport hU π hk f g h).action r) x hx

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
