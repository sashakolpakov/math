import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointPairs
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareTransportClass

/-! # Class Invariance -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed product relation preserves the actual
Poincare line-bundle class. This is deduced from the full PEL comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincare_class_invariant (hrigid : U.PrescribedRigid) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (U.prescribedPoincareTarget π hU hk).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf U.prescribedPoincareLine) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf U.prescribedPoincareLine) := by
  let A := U.forgetAuxiliary.data.polarized.abelian
  let D := U.forgetAuxiliary.data.polarized.dual
  let c := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  let f := c ≫ U.prescribedPoincareProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPoincareProjection
  let e := U.prescribedTransport hU π hk f g h
  let p : Over.mk f.left ⟶ D.abelian.scheme ⊗ A.scheme := Over.homMk c.left rfl
  let q : Over.mk g.left ⟶ D.abelian.scheme ⊗ A.scheme :=
    Over.homMk (U.prescribedPoincareTarget π hU hk).left
      (congrArg Over.Hom.left (U.prescribedPoincareTarget_projection π hU hk))
  have hd : Family.PointBaseChange.FamilyPointTransport.transport D.abelian.scheme f.left g.left e.polarized.dual
      (p ≫ fst _ _).left (p ≫ fst _ _).w = (q ≫ fst _ _).left := by
    have he := U.prescribedDualRelation_lift_target_of_base hU π hk hrigid
      (c ≫ U.prescribedPoincareDual) f g (Category.assoc _ _ _) h
    exact he.symm.trans (congrArg Over.Hom.left (U.prescribedPoincareTarget_dual π hU hk)).symm
  have ha : Family.PointBaseChange.FamilyPointTransport.transport A.scheme f.left g.left e.polarized.abelian
      (p ≫ snd _ _).left (p ≫ snd _ _).w = (q ≫ snd _ _).left := by
    have he := U.prescribedRelation_lift_target_of_base hU π hk hrigid
      (c ≫ U.prescribedPoincareAbelian) f g (by
        rw [Category.assoc, U.prescribedPoincareAbelian_projection]) h
    exact he.symm.trans (congrArg Over.Hom.left (U.prescribedPoincareTarget_abelian π hU hk)).symm
  have ht := Family.PointPairs.FamilyPointTransport.liftPair_transport_poincare f.left A D g.left p q
    e.polarized.dual e.polarized.abelian hd ha
  have hs := Family.PointPairs.FamilyPointTransport.liftPair_poincare f.left A D p
  have he := PoincareTransportClass.poincare_transport_class U.forgetAuxiliary.data f.left g.left e
    (Family.PointPairs.FamilyPointTransport.liftPair D.abelian.scheme A.scheme f.left p)
  rw [ht, hs] at he
  exact he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
