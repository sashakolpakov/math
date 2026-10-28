import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointZero

/-! # Zero Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual zero section respects the prescribed-family relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZero : X ⟶ U.prescribedDualTotalSpace :=
  Over.homMk (MonObj.one : 𝟙_ (Over X.left) ⟶
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme).left (by
      change _ ≫ (U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom ≫ X.hom) = X.hom
      rw [← Category.assoc, (MonObj.one : 𝟙_ (Over X.left) ⟶
        U.forgetAuxiliary.data.polarized.dual.abelian.scheme).w]
      exact Category.id_comp X.hom)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZero_projection : U.prescribedDualZero ≫ U.prescribedDualProjection = 𝟙 X :=
  Over.OverMorphism.ext (MonObj.one : 𝟙_ (Over X.left) ⟶
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme).w

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZeroOverlap : IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ U.prescribedDualOverlap π :=
  pullback.lift (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedDualZero)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (by
      rw [Category.assoc, ← Category.assoc U.prescribedDualZero, U.prescribedDualZero_projection,
        Category.id_comp]
      exact Over.OverMorphism.ext hk.w)

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZeroOverlap_source :
    U.prescribedDualZeroOverlap hU π hk ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedDualZero := pullback.lift_fst _ _ _

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZeroOverlap_base :
    U.prescribedDualZeroOverlap hU π hk ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualZeroOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedDualZeroOverlap hU π hk ≫ U.prescribedDualOverlapTarget hU π hk =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU ≫ U.prescribedDualZero := by
  let a := U.prescribedDualProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedDualZeroOverlap hU π hk
  let f' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L
  let g' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have h' : f' ≫ π = g' ≫ π := Over.OverMorphism.ext hk.w
  have hf : k ≫ f = f' := by
    change k ≫ src ≫ a = f'
    rw [← Category.assoc, U.prescribedDualZeroOverlap_source, Category.assoc,
      U.prescribedDualZero_projection, Category.comp_id]
  have hg : k ≫ g = g' := U.prescribedDualZeroOverlap_base hU π hk
  have hn := U.prescribedDualPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hpoints := U.prescribedDualPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f' g'
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h) h' hf hg
    (k.left ≫ src.left) (f'.left ≫ U.prescribedDualZero.left) rfl
    (1 : Over.mk f'.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme).w
    (congrArg Over.Hom.left (U.prescribedDualZeroOverlap_source hU π hk))
  have : IsMonHom (U.prescribedTransport hU π hk f' g' h').polarized.dual.hom :=
    (U.prescribedTransport hU π hk f' g' h').polarized.dualGroup
  have hz := Family.PointZero.FamilyPointTransport.transport_one U.forgetAuxiliary.data.polarized.dual.abelian.scheme
    f'.left g'.left (U.prescribedTransport hU π hk f' g' h').polarized.dual
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hz)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
