import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarFunctor
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NaturalGroupComparison

/-! # Scalar Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison

noncomputable section

section

/-! The literal scalar-changed total family is naturally isomorphic
to native relative pullback along the scalar-changed parameter projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def relativeScalarNativeComparison {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) (A : Over X.left) :
    (ScalarFunctor.relativeScalarFunctor b X).obj A ≅ (Over.pullback (pullback.fst X.hom b)).obj A :=
  let a : (Over.map X.hom).obj A ⟶ X := Over.homMk A.hom rfl
  Over.isoMk (Specialization.base_change_square b a).isoPullback (Specialization.base_change_square b a).isoPullback_hom_snd

theorem relativeScalarNativeComparison_fst {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) (A : Over X.left) :
    (relativeScalarNativeComparison b X A).hom.left ≫ pullback.fst A.hom (pullback.fst X.hom b) =
      pullback.fst ((Over.map X.hom).obj A).hom b :=
  (Specialization.base_change_square b (Over.homMk A.hom : (Over.map X.hom).obj A ⟶ X)).isoPullback_hom_fst

def relativeScalarNativeIso {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) :
    ScalarFunctor.relativeScalarFunctor b X ≅ Over.pullback (pullback.fst X.hom b) :=
  NatIso.ofComponents (relativeScalarNativeComparison b X) (by
    intro A B f
    let H := ScalarFunctor.relativeScalarFunctor b X
    let F := Over.pullback (pullback.fst X.hom b)
    let eA := relativeScalarNativeComparison b X A
    let eB := relativeScalarNativeComparison b X B
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((H.map f).left ≫ eB.hom.left) ≫ pullback.fst B.hom (pullback.fst X.hom b) =
        (eA.hom.left ≫ (F.map f).left) ≫ pullback.fst B.hom (pullback.fst X.hom b)
      rw [Category.assoc, relativeScalarNativeComparison_fst, Category.assoc, Cartesian.FamilyMorphismComparison.over_pullback_map_fst,
        ← Category.assoc, relativeScalarNativeComparison_fst]
      exact Cartesian.FamilyMorphismComparison.over_pullback_map_fst b ((Over.map X.hom).map f)
    · exact (H.map f ≫ eB.hom).w.trans (eA.hom ≫ F.map f).w.symm)

theorem relativeScalarNativeComparison_isMonHom {S T : Scheme.{0}} (b : T ⟶ S)
    (X : Over S) (A : Over X.left) [GrpObj A] : IsMonHom (relativeScalarNativeComparison b X A).hom :=
  NaturalGroupComparison.natural_group_comparison (ScalarFunctor.relativeScalarFunctor b X) (Over.pullback (pullback.fst X.hom b))
    (relativeScalarNativeIso b X) A

end

/-! The two projections of an actual scalar-changed family point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) (A : Over X.left)
    {W : Over S} (r : W ⟶ (Over.map X.hom).obj A)

theorem relativeScalar_point_fst :
    ((Over.pullback b).map r).left ≫ (relativeScalarNativeComparison b X A).hom.left ≫
        pullback.fst A.hom (pullback.fst X.hom b) =
      pullback.fst W.hom b ≫ r.left := by
  rw [relativeScalarNativeComparison_fst]
  exact Cartesian.FamilyMorphismComparison.over_pullback_map_fst b r

theorem relativeScalar_point_base :
    ((Over.pullback b).map r).left ≫ (relativeScalarNativeComparison b X A).hom.left ≫
        pullback.snd A.hom (pullback.fst X.hom b) =
      ((Over.pullback b).map (r ≫ (Over.homMk A.hom : (Over.map X.hom).obj A ⟶ X))).left := by
  have hw : (relativeScalarNativeComparison b X A).hom.left ≫
      pullback.snd A.hom (pullback.fst X.hom b) =
        ((Over.pullback b).map (Over.homMk A.hom : (Over.map X.hom).obj A ⟶ X)).left :=
    (relativeScalarNativeComparison b X A).hom.w
  rw [hw]
  exact (congrArg Over.Hom.left ((Over.pullback b).map_comp r (Over.homMk A.hom))).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison
