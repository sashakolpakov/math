import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.ZeroRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.InverseRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PairSpace

/-! # Scalar Group Operations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The literal scalar-changed family has its canonical group structure;
identify its three operations with the scalar-changed original diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_scalar_one :
    (MonObj.one : 𝟙_ (Over ((Over.pullback b).obj X).left) ⟶
      (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.abelian.scheme).left =
        ((Over.pullback b).map U.prescribedZero).left := by
  let G := U.forgetAuxiliary.data.polarized.abelian.scheme
  let H := Relative.ScalarFunctor.relativeScalarFunctor b X
  let F := Over.pullback b
  let v : (Over.map X.hom).obj (𝟙_ (Over X.left)) ⟶ X := Over.homMk (𝟙 X.left) rfl
  have h : (Over.map X.hom).map (MonObj.one : 𝟙_ (Over X.left) ⟶ G) = v ≫ U.prescribedZero := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  have hmap : (H.map (MonObj.one : 𝟙_ (Over X.left) ⟶ G)).left =
      (H.obj (𝟙_ (Over X.left))).hom ≫ (F.map U.prescribedZero).left := by
    rw [Relative.ScalarFunctor.relativeScalarFunctor_map_left, h, F.map_comp, Over.comp_left]
    rfl
  change ((Functor.LaxMonoidal.ε H).left ≫
    (H.map (MonObj.one : 𝟙_ (Over X.left) ⟶ G)).left) = _
  calc
    _ = (Functor.LaxMonoidal.ε H).left ≫
        ((H.obj (𝟙_ (Over X.left))).hom ≫ (F.map U.prescribedZero).left) :=
      congrArg (fun k => (Functor.LaxMonoidal.ε H).left ≫ k) hmap
    _ = ((Functor.LaxMonoidal.ε H).left ≫ (H.obj (𝟙_ (Over X.left))).hom) ≫
        (F.map U.prescribedZero).left := (Category.assoc _ _ _).symm
    _ = (F.map U.prescribedZero).left :=
      (congrArg (fun k => k ≫ (F.map U.prescribedZero).left)
        (Functor.LaxMonoidal.ε H).w).trans (Category.id_comp _)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_scalar_inverse :
    (GrpObj.inv : (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.abelian.scheme ⟶
      (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.abelian.scheme).left =
        ((Over.pullback b).map U.prescribedInverse).left := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_scalar_mul :
    let G := U.forgetAuxiliary.data.polarized.abelian.scheme
    let H := Relative.ScalarFunctor.relativeScalarFunctor b X
    (MonObj.mul : H.obj G ⊗ H.obj G ⟶ H.obj G).left =
      (Functor.LaxMonoidal.μ H G G).left ≫ ((Over.pullback b).map U.prescribedMul).left := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
