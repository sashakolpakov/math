import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TransportCocycle
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Inverse Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Inversion of the actual universal dual abelian family preserves its
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

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverse : U.prescribedDualTotalSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map
    (GrpObj.inv : U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverse_projection : U.prescribedDualInverse ≫ U.prescribedDualProjection = U.prescribedDualProjection :=
  Over.OverMorphism.ext (GrpObj.inv : U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⟶
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme).w

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverseOverlap (π : X ⟶ Q) : U.prescribedDualOverlap π ⟶ U.prescribedDualOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualInverse)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedDualInverse, U.prescribedDualInverse_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverseOverlap_source (π : X ⟶ Q) :
    U.prescribedDualInverseOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualInverse := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverseOverlap_base (π : X ⟶ Q) :
    U.prescribedDualInverseOverlap π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection := pullback.lift_snd _ _ _

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualInverseOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedDualInverseOverlap π ≫ U.prescribedDualOverlapTarget hU π hk =
      U.prescribedDualOverlapTarget hU π hk ≫ U.prescribedDualInverse := by
  let a := U.prescribedDualProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let f := src ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let k := U.prescribedDualInverseOverlap π
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have hf : k ≫ f = f := by
    change k ≫ src ≫ a = src ≫ a
    rw [← Category.assoc, U.prescribedDualInverseOverlap_source, Category.assoc, U.prescribedDualInverse_projection]
  have hg : k ≫ g = g := U.prescribedDualInverseOverlap_base π
  let x : Over.mk f.left ⟶ U.forgetAuxiliary.data.polarized.dual.abelian.scheme := Over.homMk src.left rfl
  have hn := U.prescribedDualPointTransport_natural hU π hk hrigid f g h src.left rfl k
  have hpoints := U.prescribedDualPointTransport_congr hU π hk
    (k ≫ f) (k ≫ g) f g
    (by simpa only [Category.assoc] using congrArg (fun m => k ≫ m) h) h hf hg
    (k.left ≫ src.left) (x⁻¹).left rfl (x⁻¹).w
    (congrArg Over.Hom.left (U.prescribedDualInverseOverlap_source π))
  have : IsMonHom (U.prescribedTransport hU π hk f g h).polarized.dual.hom :=
    (U.prescribedTransport hU π hk f g h).polarized.dualGroup
  have hi := Family.PointEq.FamilyPointTransport.transport_inv U.forgetAuxiliary.data.polarized.dual.abelian.scheme
    f.left g.left (U.prescribedTransport hU π hk f g h).polarized.dual x
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hpoints.trans hi)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
