import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Freeness

/-! # Joint Monicity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.JointMonicity.IntegralAuxiliaryAction

noncomputable section

/-! The auxiliary relation is jointly monic on every scheme, including
nonreduced tests. Its labels are detected at residue-field points, where
the established reduced-family rigidity applies. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem jointlyMono (hrigid : U.PrescribedRigid) :
    JointlyMono₂ (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) where
  right_cancellation {T} f g hs ht := by
    apply prod.hom_ext
    · exact hs
    · apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T).injective
      apply LocallyConstant.ext
      intro x
      let k := T.left.residueField x
      let b := T.left.fromSpecResidueField x
      let W : Over (Spec (.of R)) := Over.mk (b ≫ T.hom)
      let p : W ⟶ T := Over.homMk b rfl
      have : IsReduced W.left := inferInstanceAs (IsReduced (Spec (.of k)))
      have hsp : (p ≫ f) ≫ ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L = (p ≫ g) ≫ ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L := by
        simpa only [Category.assoc] using congrArg (fun a => p ≫ a) hs
      have htp : (p ≫ f) ≫ ActionSpace.IntegralAuxiliaryAction.target U hU = (p ≫ g) ≫ ActionSpace.IntegralAuxiliaryAction.target U hU := by
        simpa only [Category.assoc] using congrArg (fun a => p ≫ a) ht
      have hf := ActionSpace.IntegralAuxiliaryAction.target_points U hU W (p ≫ f)
      rw [hsp] at hf
      have he : ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L W (p ≫ f) = ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L W (p ≫ g) :=
        U.auxiliaryRelabelAt_injective hU hrigid ((p ≫ g) ≫ ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L)
          (hf.symm.trans (htp.trans (ActionSpace.IntegralAuxiliaryAction.target_points U hU W (p ≫ g))))
      rw [ActionPoints.IntegralAuxiliaryAction.labels_comp, ActionPoints.IntegralAuxiliaryAction.labels_comp] at he
      have hv := congrArg (fun c => c (IsLocalRing.closedPoint k)) he
      change ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L T f (p.left (IsLocalRing.closedPoint k)) =
        ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L T g (p.left (IsLocalRing.closedPoint k)) at hv
      have hp : p.left (IsLocalRing.closedPoint k) = x := T.left.fromSpecResidueField_apply x _
      rw [hp] at hv
      exact hv

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.JointMonicity.IntegralAuxiliaryAction
