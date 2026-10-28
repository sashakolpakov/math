import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap

/-! # Zero Target -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The prescribed PEL transport preserves the abelian zero section
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZeroOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedPoincareZeroOverlap π ≫ U.prescribedPoincareTarget π hU hk =
      U.prescribedDualOverlapTarget hU π hk ≫ U.prescribedPoincareZero := by
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection
  let f := src ≫ U.prescribedDualProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection
  let k := U.prescribedPoincareZeroOverlap π ≫ U.prescribedPoincareOverlapAbelian π
  have hfg : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection
  have hz : (f ≫ U.prescribedZero) ≫ U.prescribedProjection = f := by
    rw [Category.assoc, U.prescribedZero_projection, Category.comp_id]
  have hcond : (f ≫ U.prescribedZero) ≫ (U.prescribedProjection ≫ π) = g ≫ π := by
    rw [← Category.assoc, hz]
    exact hfg
  have hks : k ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection = f ≫ U.prescribedZero := by
    change (U.prescribedPoincareZeroOverlap π ≫ U.prescribedPoincareOverlapAbelian π) ≫ _ = _
    rw [Category.assoc, U.prescribedPoincareOverlapAbelian_source, ← Category.assoc,
      U.prescribedPoincareZeroOverlap_source, Category.assoc, U.prescribedPoincareZero_abelian,
      ← Category.assoc]
  have hkb : k ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection = g := by
    change (U.prescribedPoincareZeroOverlap π ≫ U.prescribedPoincareOverlapAbelian π) ≫ _ = _
    simp only [Category.assoc, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapAbelian, DescentCocycleChange.DescentCocycle.base, pullback.lift_snd]
    exact U.prescribedPoincareZeroOverlap_base π
  have hkl : k = pullback.lift (f ≫ U.prescribedZero) g hcond := by
    apply pullback.hom_ext
    · exact hks.trans (pullback.lift_fst _ _ _).symm
    · exact hkb.trans (pullback.lift_snd _ _ _).symm
  have hn := U.prescribedRelation_lift_target_of_base hU π hk hrigid
    (f ≫ U.prescribedZero) f g hz hfg
  have hc : k ≫ U.prescribedOverlapTarget hU π hk = g ≫ U.prescribedZero := by
    apply Over.OverMorphism.ext
    have hpoint := (congrArg (fun j => (j ≫ U.prescribedOverlapTarget hU π hk).left) hkl).trans hn
    have : IsMonHom (U.prescribedTransport hU π hk f g hfg).polarized.abelian.hom :=
      (U.prescribedTransport hU π hk f g hfg).polarized.abelianGroup
    exact hpoint.trans (Family.PointZero.FamilyPointTransport.transport_one
      U.forgetAuxiliary.data.polarized.abelian.scheme f.left g.left
        (U.prescribedTransport hU π hk f g hfg).polarized.abelian)
  apply U.prescribedPoincare_square.hom_ext
  · rw [Category.assoc, U.prescribedPoincareTarget_dual, ← Category.assoc,
      U.prescribedPoincareZeroOverlap_dual, Category.id_comp, Category.assoc,
      U.prescribedPoincareZero_dual, Category.comp_id]
  · rw [Category.assoc, U.prescribedPoincareTarget_abelian, ← Category.assoc, hc,
      Category.assoc, U.prescribedPoincareZero_abelian, ← Category.assoc,
      U.prescribedDualOverlapTarget_base]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
