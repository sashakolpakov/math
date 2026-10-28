import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Inverse Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Inversion of the actual universal abelian family preserves its
constructed descent relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverse : U.prescribedTotalSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map
    (GrpObj.inv : U.forgetAuxiliary.data.polarized.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverse_projection : U.prescribedInverse ≫ U.prescribedProjection = U.prescribedProjection :=
  Over.OverMorphism.ext (GrpObj.inv : U.forgetAuxiliary.data.polarized.abelian.scheme ⟶
    U.forgetAuxiliary.data.polarized.abelian.scheme).w

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverseOverlap (π : X ⟶ Q) : U.prescribedOverlap π ⟶ U.prescribedOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedInverse)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedInverse, U.prescribedInverse_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverseOverlap_source (π : X ⟶ Q) :
    U.prescribedInverseOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedInverse := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverseOverlap_base (π : X ⟶ Q) :
    U.prescribedInverseOverlap π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedProjection := pullback.lift_snd _ _ _

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedInverseOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedInverseOverlap π ≫ U.prescribedOverlapTarget hU π hk =
      U.prescribedOverlapTarget hU π hk ≫ U.prescribedInverse := by
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedInverseOverlap π
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hf : k ≫ f = f := by
    change k ≫ src ≫ a = src ≫ a
    rw [← Category.assoc, U.prescribedInverseOverlap_source, Category.assoc, U.prescribedInverse_projection]
  have hg : k ≫ g = g := U.prescribedInverseOverlap_base π
  let x : Over.mk f.left ⟶ U.forgetAuxiliary.data.polarized.abelian.scheme := Over.homMk src.left rfl
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hpoints := U.prescribedPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f g
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h) h hf hg
    (k.left ≫ src.left) (x⁻¹).left rfl (x⁻¹).w
    (congrArg Over.Hom.left (U.prescribedInverseOverlap_source π))
  have : IsMonHom (U.prescribedTransport hU π hk f g h).polarized.abelian.hom :=
    (U.prescribedTransport hU π hk f g h).polarized.abelianGroup
  have hi := Family.PointEq.FamilyPointTransport.transport_inv U.forgetAuxiliary.data.polarized.abelian.scheme
    f.left g.left (U.prescribedTransport hU π hk f g h).polarized.abelian x
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hi)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
