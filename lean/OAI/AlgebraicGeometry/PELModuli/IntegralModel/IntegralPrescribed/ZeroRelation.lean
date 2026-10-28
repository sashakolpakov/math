import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle
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

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZero : X ⟶ U.prescribedTotalSpace :=
  Over.homMk (MonObj.one : 𝟙_ (Over X.left) ⟶
    U.forgetAuxiliary.data.polarized.abelian.scheme).left (by
      change _ ≫ (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ X.hom) = X.hom
      rw [← Category.assoc, (MonObj.one : 𝟙_ (Over X.left) ⟶
        U.forgetAuxiliary.data.polarized.abelian.scheme).w]
      exact Category.id_comp X.hom)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZero_projection : U.prescribedZero ≫ U.prescribedProjection = 𝟙 X :=
  Over.OverMorphism.ext (MonObj.one : 𝟙_ (Over X.left) ⟶
    U.forgetAuxiliary.data.polarized.abelian.scheme).w

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZeroOverlap : IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ U.prescribedOverlap π :=
  pullback.lift (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedZero)
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU) (by
      rw [Category.assoc, ← Category.assoc U.prescribedZero, U.prescribedZero_projection,
        Category.id_comp]
      exact Over.OverMorphism.ext hk.w)

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZeroOverlap_source :
    U.prescribedZeroOverlap hU π hk ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L ≫ U.prescribedZero := pullback.lift_fst _ _ _

omit [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZeroOverlap_base :
    U.prescribedZeroOverlap hU π hk ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedZeroOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedZeroOverlap hU π hk ≫ U.prescribedOverlapTarget hU π hk =
      IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU ≫ U.prescribedZero := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedZeroOverlap hU π hk
  let f' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L
  let g' := IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have h' : f' ≫ π = g' ≫ π := Over.OverMorphism.ext hk.w
  have hf : k ≫ f = f' := by
    change k ≫ src ≫ a = f'
    rw [← Category.assoc, U.prescribedZeroOverlap_source, Category.assoc,
      U.prescribedZero_projection, Category.comp_id]
  have hg : k ≫ g = g' := U.prescribedZeroOverlap_base hU π hk
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hpoints := U.prescribedPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f' g'
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h) h' hf hg
    (k.left ≫ src.left) (f'.left ≫ U.prescribedZero.left) rfl
    (1 : Over.mk f'.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme).w
    (congrArg Over.Hom.left (U.prescribedZeroOverlap_source hU π hk))
  have : IsMonHom (U.prescribedTransport hU π hk f' g' h').polarized.abelian.hom :=
    (U.prescribedTransport hU π hk f' g' h').polarized.abelianGroup
  have hz := Family.PointZero.FamilyPointTransport.transport_one U.forgetAuxiliary.data.polarized.abelian.scheme
    f'.left g'.left (U.prescribedTransport hU π hk f' g' h').polarized.abelian
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hz)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
