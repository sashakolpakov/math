import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SectionPullback

/-! # Scalar Section Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarSectionComparison

noncomputable section

/-! The literal scalar change of a section agrees with its native
group-section pullback under the actual cartesian comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S) (A : Over X.left) [GrpObj A]

theorem relativeScalarSection_native
    (z : Over.mk (𝟙 X.left) ⟶ A)
    (m : X ⟶ (Over.map X.hom).obj A) (hm : m.left = z.left)
    (hz : m ≫ (Over.homMk A.hom : (Over.map X.hom).obj A ⟶ X) = 𝟙 X) :
    ((Over.pullback b).map m).left ≫ (ScalarIntrinsicComparison.relativeScalarNativeComparison b X A).hom.left =
      (Group.SectionPullback.groupSectionPullback A (pullback.fst X.hom b) z).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, ScalarIntrinsicComparison.relativeScalarNativeComparison_fst,
      Group.SectionPullback.groupSectionPullback_fst]
    exact (Cartesian.FamilyMorphismComparison.over_pullback_map_fst b m).trans (congrArg (fun f => pullback.fst X.hom b ≫ f) hm)
  · have he := (ScalarIntrinsicComparison.relativeScalarNativeComparison b X A).hom.w
    change _ ≫ pullback.snd A.hom (pullback.fst X.hom b) =
      ((Over.pullback b).map (Over.homMk A.hom : (Over.map X.hom).obj A ⟶ X)).left at he
    have h := congrArg (fun f => ((Over.pullback b).map f).left) hz
    simp only [(Over.pullback b).map_comp, (Over.pullback b).map_id, Over.comp_left, Over.id_left] at h
    rw [Category.assoc, he]
    exact h.trans (Group.SectionPullback.groupSectionPullback A (pullback.fst X.hom b) z).w.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarSectionComparison
