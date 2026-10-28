import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualZero

/-! # Dual Zero Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! The dual-zero section gives an actual section of the Poincare
overlap over the abelian-family overlap. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroOverlap (π : X ⟶ Q) :
    U.prescribedOverlap π ⟶ U.prescribedPoincareOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedPoincareDualZero)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedPoincareDualZero, U.prescribedPoincareDualZero_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroOverlap_source (π : X ⟶ Q) :
    U.prescribedPoincareDualZeroOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedPoincareDualZero :=
  pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroOverlap_base (π : X ⟶ Q) :
    U.prescribedPoincareDualZeroOverlap π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedProjection := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroOverlap_abelian (π : X ⟶ Q) :
    U.prescribedPoincareDualZeroOverlap π ≫ U.prescribedPoincareOverlapAbelian π =
      𝟙 (U.prescribedOverlap π) := by
  apply pullback.hom_ext
  · change (_ ≫ U.prescribedPoincareOverlapAbelian π) ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection = _
    rw [Category.assoc, U.prescribedPoincareOverlapAbelian_source, ← Category.assoc,
      U.prescribedPoincareDualZeroOverlap_source, Category.assoc, U.prescribedPoincareDualZero_abelian,
      Category.comp_id, Category.id_comp]
  · change (_ ≫ U.prescribedPoincareOverlapAbelian π) ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection = _
    simp only [Category.assoc, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapAbelian, DescentCocycleChange.DescentCocycle.base,
      pullback.lift_snd, Category.id_comp]
    exact U.prescribedPoincareDualZeroOverlap_base π

end

/-! The prescribed PEL transport preserves the dual-zero section
on the actual Poincare overlap. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareDualZeroOverlap π ≫ U.prescribedPoincareTarget π hU hk =
      U.prescribedOverlapTarget hU π hk ≫ U.prescribedPoincareDualZero := by
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedProjection
  let f := src ≫ U.prescribedProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedProjection
  let k := U.prescribedPoincareDualZeroOverlap π ≫ U.prescribedPoincareOverlapDual π
  have hfg : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedProjection
  have hz : (f ≫ U.prescribedDualZero) ≫ U.prescribedDualProjection = f := by
    rw [Category.assoc, U.prescribedDualZero_projection, Category.comp_id]
  have hcond : (f ≫ U.prescribedDualZero) ≫ (U.prescribedDualProjection ≫ π) = g ≫ π := by
    rw [← Category.assoc, hz]
    exact hfg
  have hks : k ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection = f ≫ U.prescribedDualZero := by
    change (U.prescribedPoincareDualZeroOverlap π ≫ U.prescribedPoincareOverlapDual π) ≫ _ = _
    rw [Category.assoc, U.prescribedPoincareOverlapDual_source, ← Category.assoc,
      U.prescribedPoincareDualZeroOverlap_source, Category.assoc, U.prescribedPoincareDualZero_dual,
      ← Category.assoc]
  have hkb : k ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection = g := by
    change (U.prescribedPoincareDualZeroOverlap π ≫ U.prescribedPoincareOverlapDual π) ≫ _ = _
    simp only [Category.assoc, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual, DescentCocycleChange.DescentCocycle.base, pullback.lift_snd]
    exact U.prescribedPoincareDualZeroOverlap_base π
  have hkl : k = pullback.lift (f ≫ U.prescribedDualZero) g hcond := by
    apply pullback.hom_ext
    · exact hks.trans (pullback.lift_fst _ _ _).symm
    · exact hkb.trans (pullback.lift_snd _ _ _).symm
  have hn := U.prescribedDualRelation_lift_target_of_base hU π hk hrigid
    (f ≫ U.prescribedDualZero) f g hz hfg
  have hc : k ≫ U.prescribedDualOverlapTarget hU π hk = g ≫ U.prescribedDualZero := by
    apply Over.OverMorphism.ext
    have hpoint := (congrArg (fun j => (j ≫ U.prescribedDualOverlapTarget hU π hk).left) hkl).trans hn
    have : IsMonHom (U.prescribedTransport hU π hk f g hfg).polarized.dual.hom :=
      (U.prescribedTransport hU π hk f g hfg).polarized.dualGroup
    exact hpoint.trans (Family.PointZero.FamilyPointTransport.transport_one
      U.forgetAuxiliary.data.polarized.dual.abelian.scheme f.left g.left
        (U.prescribedTransport hU π hk f g hfg).polarized.dual)
  apply U.prescribedPoincare_square.hom_ext
  · rw [Category.assoc, U.prescribedPoincareTarget_dual, ← Category.assoc, hc,
      Category.assoc, U.prescribedPoincareDualZero_dual, ← Category.assoc,
      U.prescribedOverlapTarget_base]
  · rw [Category.assoc, U.prescribedPoincareTarget_abelian, ← Category.assoc,
      U.prescribedPoincareDualZeroOverlap_abelian, Category.id_comp, Category.assoc,
      U.prescribedPoincareDualZero_abelian, Category.comp_id]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
